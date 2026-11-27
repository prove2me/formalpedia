-- Prove2me | solution 1 for CompanionTheory.Mirab.Irr.mirabInduced_isIrreducible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:24:09.761875+00:00
-- url     : https://prove2.me/submissions/98da47bb-5cfc-4042-a69f-902e8e8e0fce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_BlockTriangularOfSubOne
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicIsMackey
import Definitions.Def_CompanionTheory_AutomorphicTheory_MirabolicRestriction_MirabolicInduction_IndIrr
import Theorems.Thm_CompanionTheory_Mirab_Irr_deltaU_one
import Theorems.Thm_CompanionTheory_Mirab_Irr_deltaU_mem
import Theorems.Thm_CompanionTheory_Mirab_Irr_avg_apply
import Theorems.Thm_CompanionTheory_Mirab_Irr_avg_right
import Theorems.Thm_CompanionTheory_Mirab_Irr_avg_one
import Theorems.Thm_CompanionTheory_Mirab_Irr_sum_translate
import Theorems.Thm_GlobalTheory_FiniteGL_genericLine_apply
import Theorems.Thm_GlobalTheory_FiniteGL_mirabInduced_apply
import Theorems.Thm_GlobalTheory_FiniteGL_restrictMirab_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FiniteGL.genericLine_apply
attribute [local simp] GlobalTheory.FiniteGL.mirabInduced_apply
attribute [local simp] GlobalTheory.FiniteGL.restrictMirab_apply



set_option autoImplicit false
noncomputable section
open GlobalTheory.FiniteGL Formalism.L2.Indef.Tree Formalism.EigenvalueLevelCeiling
open CompanionTheory CompanionTheory.Mirab CompanionTheory.Mirab.Irr
variable {k : Type} [Field k] [Fintype k] (n : ℕ)
namespace CompanionTheory.Mirab.Irr
theorem _root_.solution (ψ₀ : AddChar k ℂ) (hψ : ψ₀ ≠ 1) : (mirabInduced n ψ₀).IsIrreducible := by
  classical
  let δ : MirabInducedSpace n ψ₀ := ⟨deltaU n ψ₀, deltaU_mem n ψ₀⟩
  have hδ : δ ≠ 0 := by
    intro h
    have h1 : (δ : mirabSub k n → ℂ) 1 = 0 := by rw [h]; rfl
    exact one_ne_zero ((deltaU_one n ψ₀).symm.trans h1)
  have hne : (⊥ : Subrepresentation (mirabInduced n ψ₀)) ≠ ⊤ := by
    intro h
    have hm : δ ∈ (⊤ : Subrepresentation (mirabInduced n ψ₀)).toSubmodule := Submodule.mem_top
    rw [← h] at hm
    exact hδ ((Submodule.mem_bot ℂ).1 hm)
  have : Nontrivial (Subrepresentation (mirabInduced n ψ₀)) := ⟨⟨⊥, ⊤, hne⟩⟩
  refine ⟨fun W => ?_⟩
  rcases eq_or_ne W ⊥ with hW | hW
  · exact Or.inl hW
  right
  obtain ⟨f, hfW, hf0⟩ : ∃ f ∈ W.toSubmodule, f ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hW (Subrepresentation.toSubmodule_injective ((Submodule.eq_bot_iff _).2 hc))
  obtain ⟨q, hq⟩ : ∃ q, (f : mirabSub k n → ℂ) q ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hf0 (Subtype.ext (funext hc))
  have hf'W : mirabInduced n ψ₀ q f ∈ W.toSubmodule := W.apply_mem_toSubmodule q hfW
  obtain ⟨F, hFdef⟩ : ∃ F : MirabInducedSpace n ψ₀, F = ∑ u : uniSub k n,
      genericChar n ψ₀ (u⁻¹) • mirabInduced n ψ₀ (u : mirabSub k n) (mirabInduced n ψ₀ q f) := ⟨_, rfl⟩
  have hFW : F ∈ W.toSubmodule := by
    rw [hFdef]
    exact Submodule.sum_mem _ (fun u _ => Submodule.smul_mem _ _ (W.apply_mem_toSubmodule _ hf'W))
  have hFx : ∀ x, (F : mirabSub k n → ℂ) x = ∑ u : uniSub k n,
      genericChar n ψ₀ (u⁻¹) * ((mirabInduced n ψ₀ q f : MirabInducedSpace n ψ₀) : mirabSub k n → ℂ) (x * u) := by
    intro x
    rw [hFdef]
    exact avg_apply n ψ₀ _ x
  have hFr : ∀ (x : mirabSub k n) (v : uniSub k n),
      (F : mirabSub k n → ℂ) (x * v) = (F : mirabSub k n → ℂ) x * genericChar n ψ₀ v := by
    intro x v
    rw [hFx, hFx]
    exact avg_right n ψ₀ _ x v
  have hF1 : (F : mirabSub k n → ℂ) 1 = (Nat.card (uniSub k n) : ℂ) * (f : mirabSub k n → ℂ) q := by
    rw [hFx, avg_one n ψ₀ _ (mirabInduced n ψ₀ q f).2, mirabInduced_apply, one_mul]
  have hcard : (Nat.card (uniSub k n) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hc : (Nat.card (uniSub k n) : ℂ) * (F : mirabSub k n → ℂ) 1 ≠ 0 := by
    rw [hF1]
    exact mul_ne_zero hcard (mul_ne_zero hcard hq)
  refine eq_top_iff.2 ?_
  intro g _
  change g ∈ W.toSubmodule
  have hg : g = ((Nat.card (uniSub k n) : ℂ) * (F : mirabSub k n → ℂ) 1)⁻¹ •
      ∑ p : mirabSub k n, (g : mirabSub k n → ℂ) p • mirabInduced n ψ₀ p⁻¹ F := by
    apply Subtype.ext
    funext x
    rw [Submodule.coe_smul, Pi.smul_apply, Submodule.coe_sum, Finset.sum_apply]
    simp only [Submodule.coe_smul, Pi.smul_apply, mirabInduced_apply, smul_eq_mul]
    rw [sum_translate n ψ₀ hψ F g F.2 hFr g.2 x, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  rw [hg]
  exact Submodule.smul_mem _ _
    (Submodule.sum_mem _ (fun p _ => Submodule.smul_mem _ _ (W.apply_mem_toSubmodule _ hFW)))
end CompanionTheory.Mirab.Irr
