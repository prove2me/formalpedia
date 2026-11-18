-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_original_negative_mark_pgf_lower_bounded_by_physical_void_20261117
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T23:37:43.410691+00:00
-- url     : https://prove2.me/submissions/5b178873-2831-4881-b2c9-9821ea5bac3c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_marked_pgf_zero_exact_exponential_20261117
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_negative_jump_joint_count_pgf_integrable_20261117
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ)
    (J : Ω → ℝ) (hJMeas : Measurable J)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
      else 0)
    (K : Ω → ℕ) (hK : Measurable K)
    (r : ℝ≥0) (hLaw : HasLaw K (poissonMeasure r) P)
    (hCount : ∀ᵐ ω ∂P, (K ω : ℝ) =
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 t ×ˢ Iio (0 : ℝ))).toReal)
    (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    Real.exp (-(r : ℝ)) ≤
      (∫ ω, z ^ (K ω) * Real.exp (θ * J ω) ∂P) := by 
  letI : IsProbabilityMeasure P := hLaw.isProbabilityMeasure
  have hZI : Integrable (fun ω => (0 : ℝ) ^ (K ω) * Real.exp (θ * J ω)) P :=
    avram_a27_original_physical_negative_jump_joint_count_pgf_integrable_20261117
      X hFinite t θ hθ J hJMeas hJEq K hK 0 (le_refl _) (by norm_num)
  have hFI : Integrable (fun ω => z ^ (K ω) * Real.exp (θ * J ω)) P :=
    avram_a27_original_physical_negative_jump_joint_count_pgf_integrable_20261117
      X hFinite t θ hθ J hJMeas hJEq K hK z hz hz1
  have hBound : ∀ᵐ ω ∂P,
      (0 : ℝ) ^ (K ω) * Real.exp (θ * J ω) ≤
        z ^ (K ω) * Real.exp (θ * J ω) := by
    filter_upwards with ω
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 0) hz _)
      (le_of_lt (Real.exp_pos _))
  calc
    Real.exp (-(r : ℝ)) =
      (∫ ω, (0 : ℝ) ^ (K ω) * Real.exp (θ * J ω) ∂P) := by
        exact (avram_a27_original_physical_marked_pgf_zero_exact_exponential_20261117
          X hFinite t θ J hJEq K r hK hLaw hCount).symm
    _ ≤ (∫ ω, z ^ (K ω) * Real.exp (θ * J ω) ∂P) :=
      integral_mono_ae hZI hFI hBound
