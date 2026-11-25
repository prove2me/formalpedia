-- Prove2me | solution 1 for Formalism.ExtensionFiltration.max_slope_minkowski
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:19:01.486966+00:00
-- url     : https://prove2.me/submissions/8e4c8f85-acb3-40dc-841a-2aef4070c84f

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_MuMaxMinkowski
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_MuMaxMinkowski
import Theorems.Thm_Formalism_ExtensionFiltration_mink_norm_sq_realize
import Theorems.Thm_Formalism_ExtensionFiltration_mink_normAt_pos
import Theorems.Thm_Formalism_ExtensionFiltration_mink_am_gm
import Theorems.Thm_Formalism_F_muMaxLeMin
import Theorems.Thm_Formalism_F_slopeLeMuMax
import Theorems.Thm_Formalism_HN_PlaceLattice_realize_injective
import Theorems.Thm_Formalism_HN_place_lattice_structure
import Theorems.Thm_Formalism_HN_sizeMu_finrank_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.ExtensionFiltration
open Formalism.HN
namespace Formalism.ExtensionFiltration
theorem _root_.solution : MuMaxMinkowski := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X hX B La hBfg hB0 hshort
  set ρ := Formalism.HermitianLatticesTheory.realize b X with hρ
  obtain ⟨hlat, hrk, -⟩ := place_lattice_structure K V ι b X hX B hBfg
  have hinj : Function.Injective ρ := PlaceLattice.realize_injective b X hX
  have hnf := sizeMu_finrank_eq K
  have hf : (0 : ℝ) < (nPl K : ℝ) := by
    have : 0 < nPl K := Fintype.card_pos
    exact_mod_cast this
  have hj : (0 : ℝ) < (rkK B : ℝ) := by
    have : Module.Finite K V := Module.Finite.of_basis b
    have h : Submodule.span K (B : Set V) ≠ ⊥ := by
      intro h
      apply hB0
      rw [Submodule.span_eq_bot] at h
      exact (Submodule.eq_bot_iff _).2 (fun x hx => h x hx)
    have : 0 < rkK (K := K) B :=
      Nat.lt_of_lt_of_le Nat.zero_lt_one (Submodule.one_le_finrank_iff.2 h)
    exact_mod_cast this
  have hdisc : DiscreteTopology (zl ρ B) := hlat.2

  have hne : ∀ N : Submodule (𝓞 K) V, N ≠ ⊥ → zl ρ N ≠ ⊥ := by
    intro N hN h
    apply hN
    refine (Submodule.eq_bot_iff _).2 fun x hx => ?_
    have hm : ρ x ∈ zl ρ N := ⟨x, hx, rfl⟩
    rw [h, Submodule.mem_bot] at hm
    exact hinj (by rw [hm, map_zero])
  have hmono : ∀ N : Submodule (𝓞 K) V, N ≤ B → zl ρ N ≤ zl ρ B := by
    rintro N hN y ⟨x, hx, rfl⟩
    exact ⟨x, hN hx, rfl⟩

  set r : ℝ := Real.sqrt (nPl K : ℝ) * Real.exp (-La) with hr
  have hr0 : 0 < r := mul_pos (Real.sqrt_pos.2 hf) (Real.exp_pos _)
  have hmin : ∀ y ∈ zl ρ B, y ≠ 0 → r ≤ ‖y‖ := by
    rintro y ⟨x, hx, rfl⟩ hy
    have hx0 : x ≠ 0 := fun h => hy (by rw [h]; exact map_zero ρ)
    have h1 := hshort x hx hx0
    have h2 := mink_am_gm (fun v => Formalism.HermitianLatticesTheory.normAt b X v x)
      (fun v => mink_normAt_pos b X hX v x hx0)
    have h3 : ‖ρ x‖ ^ 2 = ∑ v, Formalism.HermitianLatticesTheory.normAt b X v x ^ 2 := mink_norm_sq_realize b X x
    have h4 : r ^ 2 ≤ ‖ρ x‖ ^ 2 := by
      rw [h3, hr, mul_pow, Real.sq_sqrt hf.le]
      refine le_trans (mul_le_mul_of_nonneg_left ?_ hf.le) h2
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.2
      have : (1 / (nPl K : ℝ)) * ∑ v, Real.log (Formalism.HermitianLatticesTheory.normAt b X v x) =
          (1 / (Fintype.card (InfinitePlace K) : ℝ)) * ∑ v, Real.log (Formalism.HermitianLatticesTheory.normAt b X v x) := rfl
      push_cast
      linarith
    exact (pow_le_pow_iff_left₀ hr0.le (norm_nonneg _) (by norm_num)).1 h4
  have hM := Formalism.F.muMaxLeMin _ (zl ρ B) hdisc (hne B hB0) r hr0 hmin

  have hle : muMax ρ B ≤ Formalism.F.muMax (zl ρ B) := by
    refine csSup_le ⟨_, B, le_rfl, hB0, rfl⟩ ?_
    rintro t ⟨N, hN, hN0, rfl⟩
    exact Formalism.F.slopeLeMuMax _ (zl ρ B) (zl ρ N) hdisc (hmono N hN) (hne N hN0)
  have hrkR : (Formalism.F.rk (zl ρ B) : ℝ) = 2 * (nPl K : ℝ) * (rkK B : ℝ) := by
    have : Formalism.F.rk (zl ρ B) = 2 * nPl K * rkK B := by rw [← hnf]; exact hrk
    rw [this]; push_cast; ring
  have hlogr : Real.log r = Real.log (nPl K : ℝ) / 2 - La := by
    rw [hr, Real.log_mul (Real.sqrt_pos.2 hf).ne' (Real.exp_pos _).ne', Real.log_sqrt hf.le,
      Real.log_exp]
    ring
  have hlogrk : Real.log (Formalism.F.rk (zl ρ B) : ℝ) =
      Real.log 2 + Real.log (nPl K : ℝ) + Real.log (rkK B : ℝ) := by
    rw [hrkR, Real.log_mul (by positivity) hj.ne', Real.log_mul (by norm_num) hf.ne']
  rw [hlogr, hlogrk] at hM
  unfold muMaxDef
  linarith
end Formalism.ExtensionFiltration
