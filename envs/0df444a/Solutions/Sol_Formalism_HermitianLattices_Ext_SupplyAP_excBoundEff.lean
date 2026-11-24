-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.SupplyAP.excBoundEff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:22:41.460796+00:00
-- url     : https://prove2.me/submissions/c0946053-383a-47e0-abd8-ccd2b42ea07b

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_LfunctionOneLowerBound
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LDerivNearOne
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffExc
import Theorems.Thm_Formalism_HermitianLattices_Ext_SupplyAP_log_sq_le_four_mul_of_one_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_SupplyAP_lfunction_one_lower_bound
import Theorems.Thm_Formalism_ZeroFreeDirichlet_lfunction_deriv_near_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.ZeroFreeDirichlet
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.SupplyAP
namespace Formalism.HermitianLattices.Ext.SupplyAP
theorem _root_.solution : ExcBoundAt 2 := by
  obtain ⟨CD, hCD⟩ := lfunction_deriv_near_one
  set C := max CD 1 with hCdef
  have hC1 : 1 ≤ C := le_max_right _ _
  refine ⟨min (1 / 12) (1 / (480 * C)), lt_min (by norm_num) (by positivity), ?_⟩
  intro q _ χ β hχ2 hχ hz
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hq0 : (0 : ℝ) < q := by linarith
  have hq2 : (q : ℝ) ^ (-((2 : ℕ) : ℝ)) = ((q : ℝ) ^ 2)⁻¹ := by
    rw [Real.rpow_neg hq0.le, Real.rpow_natCast]
  rw [hq2]
  have hβ1 : β < 1 := by
    by_contra h
    push Not at h
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by simpa using h) hz
  set ℓ := Real.log (3 * (q : ℝ)) with hℓdef
  have hℓ1 : 1 ≤ ℓ := by
    have h3 : Real.exp 1 ≤ 3 * (q : ℝ) := by
      have := Real.exp_one_lt_d9; linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ ℓ := Real.log_le_log (Real.exp_pos 1) h3
  have hℓsq : ℓ ^ 2 ≤ 12 * q := by
    have := log_sq_le_four_mul_of_one_le (y := 3 * (q : ℝ)) (by linarith)
    linarith
  have hℓle : ℓ ≤ 12 * q := by nlinarith
  have hmin1 : min (1 / 12) (1 / (480 * C)) ≤ 1 / 12 := min_le_left _ _
  have hmin2 : min (1 / 12) (1 / (480 * C)) ≤ 1 / (480 * C) := min_le_right _ _
  have hmin0 : 0 < min (1 / 12) (1 / (480 * C)) := lt_min (by norm_num) (by positivity)
  have hqq : (0 : ℝ) < (q : ℝ) ^ 2 := by positivity
  by_cases hcase : β < 1 - 1 / ℓ
  ·
    have hinv : 1 / (12 * (q : ℝ) ^ 2) ≤ 1 / ℓ := by
      apply one_div_le_one_div_of_le (by linarith)
      nlinarith
    have : min (1 / 12) (1 / (480 * C)) * ((q : ℝ) ^ 2)⁻¹ ≤ 1 / (12 * (q : ℝ) ^ 2) := by
      rw [show 1 / (12 * (q : ℝ) ^ 2) = 1 / 12 * ((q : ℝ) ^ 2)⁻¹ by field_simp]
      exact mul_le_mul_of_nonneg_right hmin1 (by positivity)
    linarith
  · push Not at hcase
    have hf : ∀ t ∈ Set.Icc β 1, HasDerivWithinAt (fun t : ℝ => DirichletCharacter.LFunction χ (t : ℂ))
        (deriv (DirichletCharacter.LFunction χ) (t : ℂ)) (Set.Icc β 1) t := fun t _ =>
      ((DirichletCharacter.differentiable_LFunction hχ (t : ℂ)).hasDerivAt.comp_ofReal).hasDerivWithinAt
    have hbound : ∀ t ∈ Set.Ico β 1, ‖deriv (DirichletCharacter.LFunction χ) (t : ℂ)‖ ≤ C * ℓ ^ 2 := by
      intro t ht
      have h := hCD q χ hχ t (by rw [← hℓdef]; linarith [ht.1]) ht.2.le
      have : CD * Real.log (3 * q) ^ 2 ≤ C * Real.log (3 * q) ^ 2 :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
      exact h.trans (by rw [← hℓdef] at this; exact this)
    have hmv := norm_image_sub_le_of_norm_deriv_le_segment' hf hbound 1 ⟨hβ1.le, le_refl 1⟩
    simp only [Complex.ofReal_one, hz, sub_zero] at hmv
    have hL1 := lfunction_one_lower_bound q χ hχ2 hχ
    have hre : (DirichletCharacter.LFunction χ 1).re ≤ ‖DirichletCharacter.LFunction χ 1‖ :=
      Complex.re_le_norm _
    have hδ : 0 ≤ 1 - β := by linarith
    have hkey : 1 / (20 * ((q : ℝ) + 1)) ≤ C * (12 * q) * (1 - β) := by
      have : C * ℓ ^ 2 * (1 - β) ≤ C * (12 * q) * (1 - β) := by
        apply mul_le_mul_of_nonneg_right _ hδ
        exact mul_le_mul_of_nonneg_left hℓsq (by linarith)
      linarith
    have hkey2 : 1 ≤ 480 * C * (q : ℝ) ^ 2 * (1 - β) := by
      rw [div_le_iff₀ (by positivity)] at hkey
      nlinarith
    have : min (1 / 12) (1 / (480 * C)) * ((q : ℝ) ^ 2)⁻¹ ≤ 1 - β := by
      calc min (1 / 12) (1 / (480 * C)) * ((q : ℝ) ^ 2)⁻¹ ≤ 1 / (480 * C) * ((q : ℝ) ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_right hmin2 (by positivity)
        _ = 1 / (480 * C * (q : ℝ) ^ 2) := by field_simp
        _ ≤ 1 - β := by
            rw [div_le_iff₀ (by positivity)]; linarith
    linarith
end Formalism.HermitianLattices.Ext.SupplyAP
