-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_original_marked_joint_PGF_real_entire_HasSum_20261117
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T00:17:12.905018+00:00
-- url     : https://prove2.me/submissions/fe80853c-db0f-4d55-967d-34255e298f8c

import Mathlib.Probability.HasLaw
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a85_original_physical_negative_jump_exponential_integrable_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a27_poisson_real_geometric_sequence_integrable_20261117
import Theorems.Thm_AvramDividend_Classical_avram_a27_joint_marked_count_pgf_hasSum_exact_count_cell_coefficients_20261117
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
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
    (z : ℝ) :
    HasSum (fun k : ℕ => z ^ k *
      (∫ ω in {ω : Ω | K ω = k}, Real.exp (θ * J ω) ∂P))
      (∫ ω, z ^ (K ω) * Real.exp (θ * J ω) ∂P) := by
  let F : Ω → ℝ := fun ω =>
    z ^ (K ω) * Real.exp (θ * J ω)
  let B : Ω → ℝ := fun ω => |z| ^ (K ω)
  have hExp :=
    avram_a85_original_physical_negative_jump_exponential_integrable_20261114
      X hFinite t θ hθ J hJMeas hJEq
  have hPowIntegrable : Integrable B P := by
    have hModel :=
      avram_a27_poisson_real_geometric_sequence_integrable_20261117 r |z|
    have hTransport : Integrable
        (fun ω : Ω => |z| ^ (K ω)) P := by
      exact MeasureTheory.MeasurePreserving.integrable_comp_of_integrable (hLaw.measurePreserving hK) hModel
    exact hTransport
  have hMeasPow : Measurable (fun ω : Ω => z ^ (K ω)) :=
    (measurable_of_countable (fun n : ℕ => z ^ n)).comp hK
  have hMeasExp : Measurable (fun ω : Ω => Real.exp (θ * J ω)) :=
    (hJMeas.const_mul θ).exp
  have hMeasF : Measurable F := hMeasPow.mul hMeasExp
  have hDom : ∀ᵐ ω ∂P, ‖F ω‖ ≤ ‖B ω‖ := by
    filter_upwards [hExp.2] with ω he
    have hPos : 0 ≤ |z| ^ (K ω) := pow_nonneg (abs_nonneg _) _
    change ‖z ^ (K ω) * Real.exp (θ * J ω)‖ ≤
      ‖|z| ^ (K ω)‖
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    rw [abs_mul, abs_pow, abs_of_nonneg (le_of_lt he.1),
      abs_of_nonneg hPos]
    exact mul_le_of_le_one_right hPos he.2
  have hInt : Integrable F P :=
    hPowIntegrable.mono hMeasF.aestronglyMeasurable hDom
  exact
    avram_a27_joint_marked_count_pgf_hasSum_exact_count_cell_coefficients_20261117
      P K hK (fun ω => Real.exp (θ * J ω)) z hInt
