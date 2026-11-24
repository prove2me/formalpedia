-- Prove2me | solution 1 for Formalism.HN.example_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:29.360433+00:00
-- url     : https://prove2.me/submissions/6a377c41-e0cd-4c46-8352-baddea299ec8

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNSlopes
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Example
import Theorems.Thm_Formalism_HN_PolygonExample_coord0
import Theorems.Thm_Formalism_HN_PolygonExample_coord1
import Theorems.Thm_Formalism_HN_PolygonExample_discrete_of_le
import Theorems.Thm_Formalism_HN_PolygonExample_rk_Lx
import Theorems.Thm_Formalism_HN_PolygonExample_covol_Lx
import Theorems.Thm_Formalism_HN_PolygonExample_Px_le
import Theorems.Thm_P2M_Formalism_HN_PolygonExample_e__ne_bc6b4793aac7
import Theorems.Thm_Formalism_HN_PolygonExample_covol_Px
import Theorems.Thm_Formalism_HN_PolygonExample_rk_Px
import Theorems.Thm_Formalism_HN_ex_deg
import Theorems.Thm_Formalism_HN_ex_rk
import Theorems.Thm_Formalism_HN_ex_slope
import Theorems.Thm_Formalism_HN_ex_isLat
import Theorems.Thm_Formalism_HN_ex_bounds
import Theorems.Thm_Formalism_HN_ex_slopes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HN
open PolygonExample
local notation "ρx" => AddMonoidHom.id E2
namespace Formalism.HN
theorem _root_.solution (h1 : MuChar.{0, 0, 0}) (h2 : HNStep.{0, 0, 0}) (h3 : HNSlopes.{0, 0, 0}) :
    Example := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : IsLat ρx Lx := ex_isLat Lx le_rfl
  have he₀L : e₀ ∈ Lx := Submodule.subset_span (Set.mem_insert _ _)
  have he₀P : e₀ ∈ Px := Submodule.mem_span_singleton_self e₀
  have hLne : Lx ≠ ⊥ := fun h => e₀_ne (by rw [h] at he₀L; simpa using he₀L)
  have hPne : Px ≠ ⊥ := fun h => e₀_ne (by rw [h] at he₀P; simpa using he₀P)
  have rkL : rk ρx Lx = 2 := by rw [ex_rk, rk_Lx]
  have rkP : rk ρx Px = 1 := by rw [ex_rk, rk_Px]
  have degL : deg ρx Lx = - Real.log 2 := by rw [ex_deg, Formalism.F.deg, covol_Lx]
  have degP : deg ρx Px = 0 := by rw [ex_deg, Formalism.F.deg, covol_Px]; simp
  have rkbot : rk ρx (⊥ : Submodule ℤ E2) = 0 := by rw [ex_rk, Formalism.F.rk]; simp
  have bnd : ∀ N, N ≤ Lx →
      (rk ρx N ≤ 2 ∧ deg ρx N ≤ 0 ∧ (rk ρx N = 2 → deg ρx N ≤ - Real.log 2)) := by
    intro N hN
    rw [ex_rk, ex_deg]
    exact ex_bounds N hN
  have mc := fun N (hN : N ≤ Lx) (hne : N ≠ ⊥) => h1 ℤ E2 E2 ρx N (ex_isLat N hN) hne
  have mumin_le : ∀ N, N ≤ Lx → N ≠ ⊥ → muMin ρx N ≤ deg ρx N / rk ρx N := by
    intro N hN hne
    have := (mc N hN hne).2.2.2.1
    rwa [ex_slope, Formalism.F.slope, ← ex_deg, ← ex_rk] at this
  have muMax0 : muMax ρx Lx = 0 := by
    apply le_antisymm
    · refine ((mc Lx le_rfl hLne).1 0).2 (fun N hN => ?_)
      rw [zero_mul]
      exact (bnd N hN).2.1
    · have := ((mc Lx le_rfl hLne).1 (muMax ρx Lx)).1 le_rfl Px Px_le
      rw [degP, rkP] at this
      simpa using this
  have muMinL : muMin ρx Lx = - Real.log 2 := by
    apply le_antisymm
    · have := ((mc Lx le_rfl hLne).2.1 (muMin ρx Lx)).1 le_rfl Px Px_le
      rw [degP, rkP, rkL, degL] at this
      norm_num at this
      linarith
    · refine ((mc Lx le_rfl hLne).2.1 _).2 (fun N hN => ?_)
      rw [rkL, degL]
      obtain ⟨b1, b2, b3⟩ := bnd N hN
      obtain h | h | h : rk ρx N = 0 ∨ rk ρx N = 1 ∨ rk ρx N = 2 := by omega
      · rw [h]; push_cast; linarith
      · rw [h]; push_cast; linarith
      · have := b3 h
        rw [h]; push_cast; linarith
  have hs := fun θ => h2 ℤ E2 E2 ρx Lx hL θ
  have hpos : ∀ θ : ℝ, 0 < θ → hnStep ρx Lx θ = ⊥ := by
    intro θ hθ
    by_contra hne
    have hSL : hnStep ρx Lx θ ≤ Lx := (hs θ).1.1
    have h₁ := (hs θ).2.1 hne
    have h₂ := mumin_le _ hSL hne
    have h₃ : deg ρx (hnStep ρx Lx θ) / rk ρx (hnStep ρx Lx θ) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (bnd _ hSL).2.1 (Nat.cast_nonneg _)
    linarith
  have muMinP : 0 ≤ muMin ρx Px := by
    refine ((mc Px Px_le hPne).2.1 0).2 (fun N hN => ?_)
    rw [zero_mul, degP]
    linarith [(bnd N (hN.trans Px_le)).2.1]
  have step0 : hnStep ρx Lx 0 = Px := by
    have hPS : Px ≤ hnStep ρx Lx 0 := (hs 0).2.2.1 Px Px_le hPne muMinP
    have hSL : hnStep ρx Lx 0 ≤ Lx := (hs 0).1.1
    have hSne : hnStep ρx Lx 0 ≠ ⊥ := fun h => hPne (le_bot_iff.1 (h ▸ hPS))
    have hrkS : rk ρx (hnStep ρx Lx 0) ≠ 2 := by
      intro h
      have h₁ := (hs 0).2.1 hSne
      have h₂ := mumin_le _ hSL hSne
      rw [h] at h₂
      have := (bnd _ hSL).2.2 h
      push_cast at h₂
      linarith
    refine le_antisymm ?_ hPS
    intro x hx
    have hxL := hSL hx
    rw [Lx, Submodule.mem_span_pair] at hxL
    obtain ⟨m, n, hmn⟩ := hxL
    by_cases hn : n = 0
    · subst hn
      rw [← hmn]
      simp only [zero_smul, add_zero]
      exact Submodule.smul_mem _ m he₀P
    exfalso
    apply hrkS
    haveI := discrete_of_le _ hSL
    have hli : LinearIndependent ℤ
        ![(⟨e₀, hPS he₀P⟩ : hnStep ρx Lx 0), (⟨x, hx⟩ : hnStep ρx Lx 0)] := by
      apply LinearIndependent.of_comp (hnStep ρx Lx 0).subtype
      rw [show (hnStep ρx Lx 0).subtype ∘
          ![(⟨e₀, hPS he₀P⟩ : hnStep ρx Lx 0), (⟨x, hx⟩ : hnStep ρx Lx 0)] = ![e₀, x] by
        ext i : 1
        fin_cases i <;> rfl]
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have key : s • e₀ + t • x = (s + t * m) • e₀ + (t * n) • ((2 : ℝ) • e₁) := by
        rw [← hmn]
        module
      rw [key] at hst
      have c0 := congrArg (fun v : E2 => v 0) hst
      have c1 := congrArg (fun v : E2 => v 1) hst
      simp only [coord0, coord1, PiLp.zero_apply] at c0 c1
      have ht : t = 0 := by
        push_cast at c1
        have h' : (t : ℝ) * n = 0 := by linarith
        have h'' : t * n = 0 := by exact_mod_cast h'
        exact (mul_eq_zero.1 h'').resolve_right hn
      subst ht
      refine ⟨?_, rfl⟩
      simpa using c0
    have hc := hli.fintype_card_le_finrank
    simp only [Fintype.card_fin] at hc
    have hle2 := (bnd _ hSL).1
    rw [ex_rk, Formalism.F.rk] at hle2 ⊢
    omega
  have stepL : hnStep ρx Lx (- Real.log 2) = Lx :=
    le_antisymm (hs _).1.1 ((hs _).2.2.1 Lx le_rfl hLne (by rw [muMinL]))
  have hsl := h3 ℤ E2 E2 ρx Lx hL
  have hslopes := ex_slopes (rk ρx Lx) (slopeList ρx Lx) rkL hsl.1
    (fun θ hθ => by rw [hsl.2.1 θ, hpos θ hθ, rkbot])
    (by rw [hsl.2.1 0, step0, rkP])
    (by rw [hsl.2.2.1, degL])
  unfold Example
  exact ⟨hL, rkL, hslopes, step0, stepL, muMax0, muMinL⟩
end Formalism.HN
