-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_original_negative_mark_joint_PGF_convexOn_unit_interval_20261117
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T23:46:34.764546+00:00
-- url     : https://prove2.me/submissions/8d00798b-3cd7-4c60-91ae-a68639bc3a9f

import Mathlib.Analysis.Convex.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Convex.Function
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_negative_jump_joint_count_pgf_integrable_20261117
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
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
    (K : Ω → ℕ) (hK : Measurable K) :
    ConvexOn ℝ (Icc (0 : ℝ) 1)
      (fun z => ∫ ω, z ^ (K ω) * Real.exp (θ * J ω) ∂P) := by
  have hConv : ∀ᵐ ω ∂P, ConvexOn ℝ (Icc (0 : ℝ) 1)
      (fun z : ℝ => z ^ (K ω) * Real.exp (θ * J ω)) := by
    filter_upwards with ω
    have hpow : ConvexOn ℝ (Icc (0 : ℝ) 1)
        (fun z : ℝ => z ^ (K ω)) :=
      (convexOn_pow (K ω)).subset
        (fun z hz => hz.1) (convex_Icc 0 1)
    have hscaled := ConvexOn.smul (Real.exp_nonneg (θ * J ω)) hpow
    simpa only [smul_eq_mul, mul_comm] using hscaled
  have hInt : ∀ z ∈ Icc (0 : ℝ) 1,
      Integrable (fun ω => z ^ (K ω) * Real.exp (θ * J ω)) P := by
    intro z hz
    exact avram_a27_original_physical_negative_jump_joint_count_pgf_integrable_20261117
      X hFinite t θ hθ J hJMeas hJEq K hK z hz.1 hz.2
  exact integral_convexOn_of_integrand_ae (convex_Icc 0 1) hConv hInt
