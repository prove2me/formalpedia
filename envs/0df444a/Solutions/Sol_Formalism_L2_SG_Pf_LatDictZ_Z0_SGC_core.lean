-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z0.SGC.core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:36:07.320749+00:00
-- url     : https://prove2.me/submissions/4020e7be-374a-4b5a-a702-447cf19d3164

import Mathlib
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_SelfDualRestr
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_SemiGenusLocal
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z0_SGC_exists_isom_vec
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z0_SGA_exists_norm_eq
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z0_SGA_exists_unit_norm
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z0_SGB_extE_apply
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z0_SGB_extE_isom
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z0_SGB_mem_iff_split
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z0_SGB_nondeg_restr
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z0_SGB_selfDual_map
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z0_SGB_selfDual_restr
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z0_SGB_symm_restr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Module
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z0 Formalism.L2.SG.Pf.LatDictZ.Z0.SGC
open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA Formalism.L2.SG.Pf.LatDictZ.Z0.SGA Formalism.L2.SG.Pf.LatDictZ.Z0.SGB
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.L2.SG.Pf.LatDictZ.Z0.SGC
theorem _root_.solution {p : Ideal (𝓞 K)} (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hp : p.IsMaximal) (n : ℕ) :
    ∀ (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V], finrank K V = n →
    ∀ (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm → (∀ x, (∀ y, h x y = 0) → x = 0) →
    ∀ M₁ M₂ : AddSubgroup V, IsSelfDualMod (locRing p) h M₁ → IsSelfDualMod (locRing p) h M₂ →
      ∃ g : V ≃ₗ[K] V, (∀ x y, h (g x) (g y) = h x y) ∧ ∀ x, x ∈ M₁ ↔ g x ∈ M₂ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ hn h hsy hnd M₁ M₂ h1 h2
  have hs : ∀ u v, star (h u v) = h v u := fun u v => hsy.eq u v
  by_cases hV : ∃ x₀ : V, x₀ ≠ 0
  swap
  · push Not at hV
    refine ⟨LinearEquiv.refl K V, fun _ _ => rfl, fun x => ?_⟩
    rw [hV x]
    exact ⟨fun _ => M₂.zero_mem, fun _ => M₁.zero_mem⟩
  obtain ⟨x₀, hx₀⟩ := hV
  obtain ⟨e, heM, heu⟩ := exists_unit_norm hK hp hsy hnd h1 x₀ hx₀
  obtain ⟨X, hXM, hXe⟩ := exists_norm_eq hK hp hsy hnd h2 e heu
  have hXu : IsUnitIn (locRing p) (h X X) := hXe ▸ heu
  have hX0 : h X X ≠ 0 := hXu.1
  obtain ⟨τ, hτ, hτe⟩ := exists_isom_vec hsy hnd heu.1 hXe
  have hN1 := selfDual_map h1 τ hτ
  have hXN : X ∈ M₁.comap (τ.symm : V →ₗ[K] V).toAddMonoidHom := by
    change τ.symm X ∈ M₁
    rw [← hτe, LinearEquiv.symm_apply_apply]
    exact heM
  have hdim : finrank K (LinearMap.ker (h X)) < n := by
    have h1' := LinearMap.finrank_range_add_finrank_ker (h X)
    have hpos : 0 < finrank K (LinearMap.range (h X)) := by
      rw [Module.finrank_pos_iff_exists_ne_zero]
      exact ⟨⟨h X X, X, rfl⟩, fun h0 => hX0 (congrArg Subtype.val h0)⟩
    omega
  obtain ⟨g', hg', hmem'⟩ := ih _ hdim (LinearMap.ker (h X)) rfl (restr h (LinearMap.ker (h X)))
    (symm_restr hsy _) (nondeg_restr hs hnd hX0) _ _ (selfDual_restr hs hN1 hXN hXu)
    (selfDual_restr hs h2 hXM hXu)
  refine ⟨τ.trans (extE h X hX0 g'), ?_, ?_⟩
  · intro x y
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, extE_isom h X hX0 hs g' (fun u v => hg' u v), hτ]
  · intro x
    rw [LinearEquiv.trans_apply]
    have e1 : x ∈ M₁ ↔ τ x ∈ M₁.comap (τ.symm : V →ₗ[K] V).toAddMonoidHom := by
      change _ ↔ τ.symm (τ x) ∈ M₁
      rw [LinearEquiv.symm_apply_apply]
    rw [e1, mem_iff_split hN1 hXN hXu, mem_iff_split h2 hXM hXu, extE_apply, coef_ext, proj_ext]
    exact and_congr Iff.rfl (hmem' (proj h X hX0 (τ x)))
end Formalism.L2.SG.Pf.LatDictZ.Z0.SGC
