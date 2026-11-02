-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_weighted_true_increment_MemLp_two
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T12:26:35.429077+00:00
-- url     : https://prove2.me/submissions/b5823791-8d55-4dfd-b58f-770c1436499d

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0)
    (H : Ω → ℝ) (hHmeas : StronglyMeasurable H)
    (K : ℝ) (hK : 0 ≤ K) (hH : ∀ ω, |H ω| ≤ K) :
    MemLp (fun ω =>
      H ω * (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c)) 2 P := by
  classical
  let Y : Ω → ℝ := fun ω =>
    X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
  change MemLp (fun ω => H ω * Y ω) 2 P
  have hY : MemLp Y 2 P := by
    simpa only [Y] using
      avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two
        X hν τ hτ T hbounded h
  have hYm : AEStronglyMeasurable (fun ω => H ω * Y ω) P :=
    hHmeas.aestronglyMeasurable.mul hY.aestronglyMeasurable
  have hSq : Integrable (fun ω => (Y ω) ^ 2) P :=
    (memLp_two_iff_integrable_sq hY.aestronglyMeasurable).mp hY
  have hTop : Integrable (fun ω => K ^ 2 * (Y ω) ^ 2) P :=
    hSq.const_mul (K ^ 2)
  have hpoint (ω : Ω) :
      (H ω * Y ω) ^ 2 ≤ K ^ 2 * (Y ω) ^ 2 := by
    have hHa := abs_le.mp (hH ω)
    have hHsq : (H ω) ^ 2 ≤ K ^ 2 := by
      have hp : 0 ≤ (K - H ω) * (K + H ω) :=
        mul_nonneg (sub_nonneg.mpr hHa.2) (by linarith)
      nlinarith
    calc
      _ = (H ω) ^ 2 * (Y ω) ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hHsq (sq_nonneg _)
  have hWSqMeas : AEStronglyMeasurable
      (fun ω => (H ω * Y ω) ^ 2) P := by
    have ht := hYm.mul hYm
    change AEStronglyMeasurable
      (fun ω => (H ω * Y ω) * (H ω * Y ω)) P at ht
    simpa only [pow_two] using ht
  have hWInt : Integrable (fun ω => (H ω * Y ω) ^ 2) P :=
    integrable_of_le_of_le hWSqMeas
      (Filter.Eventually.of_forall (fun ω => sq_nonneg _))
      (Filter.Eventually.of_forall hpoint)
      (integrable_zero Ω ℝ P) hTop
  exact (memLp_two_iff_integrable_sq hYm).mpr hWInt
