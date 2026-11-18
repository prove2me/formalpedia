-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_original_marked_pgf_expected_le_physical_Poisson_count_pgf_20261117
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T23:25:55.619961+00:00
-- url     : https://prove2.me/submissions/23f7f5fd-819e-484f-a359-40880e137077

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.HasLaw
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a85_original_physical_negative_jump_exponential_integrable_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_negative_jump_joint_count_pgf_integrable_20261117
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_count_HasLaw_pgf_exact_20261117
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
    (K : Ω → ℕ) (hK : Measurable K)
    (r : ℝ≥0) (hLaw : HasLaw K (poissonMeasure r) P)
    (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    (∫ ω, z ^ (K ω) * Real.exp (θ * J ω) ∂P) ≤
      Real.exp ((r : ℝ) * (z - 1)) := by
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨_, hBound⟩ :=
    avram_a85_original_physical_negative_jump_exponential_integrable_20261114
      X hFinite t θ hθ J hJMeas hJEq
  have hPow (n : ℕ) : z ^ n ≤ (1 : ℝ) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ]
      calc
        z ^ n * z ≤ z ^ n * 1 :=
          mul_le_mul_of_nonneg_left hz1 (pow_nonneg hz _)
        _ = z ^ n := by ring
        _ ≤ 1 := ih
  have hMeas : Measurable (fun ω : Ω => z ^ (K ω)) :=
    (measurable_of_countable (fun n : ℕ => z ^ n)).comp hK
  have hIntCount : Integrable (fun ω : Ω => z ^ (K ω)) P := by
    apply Integrable.of_bound hMeas.aestronglyMeasurable 1
    exact Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hz _)]
      exact hPow (K ω))
  have hIntMarked :=
    avram_a27_original_physical_negative_jump_joint_count_pgf_integrable_20261117
      X hFinite t θ hθ J hJMeas hJEq K hK z hz hz1
  have hDom :
      (fun ω => z ^ (K ω) * Real.exp (θ * J ω)) ≤ᵐ[P]
      (fun ω => z ^ (K ω)) := by
    filter_upwards [hBound] with ω hw
    exact mul_le_of_le_one_right (pow_nonneg hz _) hw.2
  calc
    (∫ ω, z ^ (K ω) * Real.exp (θ * J ω) ∂P) ≤
        (∫ ω, z ^ (K ω) ∂P) :=
      integral_mono_ae hIntMarked hIntCount hDom
    _ = Real.exp ((r : ℝ) * (z - 1)) :=
      avram_a27_original_physical_count_HasLaw_pgf_exact_20261117 P K r hLaw z
