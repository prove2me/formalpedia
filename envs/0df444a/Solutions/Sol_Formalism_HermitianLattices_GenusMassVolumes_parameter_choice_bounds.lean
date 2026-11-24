-- Prove2me | solution 1 for Formalism.HermitianLattices.GenusMassVolumes.parameter_choice_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:56:53.60586+00:00
-- url     : https://prove2.me/submissions/a0f414eb-9801-4612-8d47-78b92036b34e

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_RankMulPowThreeHalvesLeFourthPower
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_GaussianIntegralFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GenusMassVolumes
open Finset MeasureTheory
namespace Formalism.HermitianLattices.GenusMassVolumes
theorem _root_.solution : ThresholdConstantRescaledEpsilonBounds := by
  intro C₁ C₂ hC₁ hC₂
  refine ⟨8 * C₁ * C₂ ^ 2, ?_⟩
  intro p q ε₀ h₀ hp hq he0 he1 hh
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hmN : 1 ≤ min p q := le_min hp hq
  have hm : (1 : ℝ) ≤ ((min p q : ℕ) : ℝ) := by exact_mod_cast hmN
  set m : ℝ := ((min p q : ℕ) : ℝ) with hmdef
  have hPe : ((p * q : ℕ) : ℝ) = (p : ℝ) * q := by push_cast; ring
  have hP : (1 : ℝ) ≤ ((p * q : ℕ) : ℝ) := by rw [hPe]; nlinarith
  set P : ℝ := ((p * q : ℕ) : ℝ) with hPdef
  have hNe : ((p + q : ℕ) : ℝ) = (p : ℝ) + q := by push_cast; ring
  have hN : (2 : ℝ) ≤ ((p + q : ℕ) : ℝ) := by rw [hNe]; linarith
  set N : ℝ := ((p + q : ℕ) : ℝ) with hNdef
  have h2P : ((2 * p * q : ℕ) : ℝ) = 2 * P := by rw [hPe]; push_cast; ring
  have hL : (1 / 2 : ℝ) < Real.log N :=
    lt_of_lt_of_le (by have := Real.log_two_gt_d9; linarith) (Real.log_le_log (by norm_num) hN)
  set L : ℝ := Real.log N with hLdef
  have hlog : Real.log (2 * P) ≤ 2 * L := by
    have : 2 * P ≤ N ^ 2 := by rw [hPe, hNe]; nlinarith [sq_nonneg ((p : ℝ) - q)]
    calc Real.log (2 * P) ≤ Real.log (N ^ 2) := Real.log_le_log (by positivity) this
      _ = 2 * L := by rw [Real.log_pow]; push_cast; rfl
  have he2 : 0 < ε₀ ^ 2 := by positivity
  have hh' : 8 * C₁ * C₂ ^ 2 * m * P ^ 3 * N * L ≤ h₀ * ε₀ ^ 2 := by
    rwa [div_le_iff₀ he2] at hh
  have hC₂0 : 0 < C₂ := by linarith
  have hP0 : 0 < P := by linarith
  have hm0 : 0 < m := by linarith
  have hN0 : 0 < N := by linarith
  have hL0 : 0 < L := by linarith
  rw [h2P]
  constructor
  · have e : h₀ * (ε₀ / (C₂ * P)) ^ 2 / (4 * m) = (h₀ * ε₀ ^ 2) / (4 * m * C₂ ^ 2 * P ^ 2) := by
      field_simp
    rw [e, le_div_iff₀ (by positivity)]
    refine le_trans ?_ hh'
    have h1 : C₁ * (2 * P) * Real.log (2 * P) * (4 * m * C₂ ^ 2 * P ^ 2) ≤
        C₁ * (2 * P) * (2 * L) * (4 * m * C₂ ^ 2 * P ^ 2) := by gcongr
    refine h1.trans ?_
    have h2 : C₁ * (2 * P) * (2 * L) * (4 * m * C₂ ^ 2 * P ^ 2) =
        (8 * C₁ * C₂ ^ 2 * m * P ^ 3 * L) * 2 := by ring
    have h3 : 8 * C₁ * C₂ ^ 2 * m * P ^ 3 * N * L = (8 * C₁ * C₂ ^ 2 * m * P ^ 3 * L) * N := by ring
    rw [h2, h3]
    exact mul_le_mul_of_nonneg_left hN (by positivity)
  · have e : ε₀ / (C₂ * P) * h₀ / 2 = (h₀ * ε₀ ^ 2) / (2 * C₂ * P * ε₀) := by
      field_simp
    rw [e, le_div_iff₀ (by positivity)]
    refine le_trans ?_ hh'
    have h1 : C₁ * N * (2 * C₂ * P * ε₀) ≤ C₁ * N * (2 * C₂ * P * (1 / 2)) := by gcongr
    refine h1.trans ?_
    have h2 : C₁ * N * (2 * C₂ * P * (1 / 2)) = (C₁ * N * C₂ * P) * 1 := by ring
    have h3 : 8 * C₁ * C₂ ^ 2 * m * P ^ 3 * N * L = (C₁ * N * C₂ * P) * (8 * C₂ * m * P ^ 2 * L) := by ring
    rw [h2, h3]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h4 : (1 : ℝ) ≤ C₂ * m * P ^ 2 := by
      have : (1 : ℝ) ≤ P ^ 2 := one_le_pow₀ hP
      have h5 : (1 : ℝ) ≤ C₂ * m := by nlinarith
      nlinarith
    nlinarith
end Formalism.HermitianLattices.GenusMassVolumes
