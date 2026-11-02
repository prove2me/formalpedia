-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_weight_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:40:02.031098+00:00
-- url     : https://prove2.me/submissions/e1a9c988-adcd-4632-8534-aee5c04cd1ba

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_source_rightCont_stopped_gaussian_quotient_L2_centered
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_source_rightCont_stopped_gaussian_cross_quotient

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false

/-- Actual Gaussian source stopped weighted energy, with exact sigma normalisation. -/
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
    (K : ℝ) (hK : 0 ≤ K) (hH : ∀ ω, |H ω| ≤ K)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    let Z : Ω → ℝ := fun ω =>
      (Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
        (h : ℝ) * X.ψ θ) - 1) / θ
    (∫ ω, (H ω * Z ω) ^ 2 ∂P) ≤
      K ^ 2 * ((Real.exp ((h : ℝ) * (X.σ ^ 2 * θ * θ)) - 1) / (θ * θ)) := by
  dsimp only
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let Z : Ω → ℝ := fun ω =>
    (Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
      (h : ℝ) * X.ψ θ) - 1) / θ
  change (∫ ω, (H ω * Z ω) ^ 2 ∂P) ≤
    K ^ 2 * ((Real.exp ((h : ℝ) * (X.σ ^ 2 * θ * θ)) - 1) / (θ * θ))
  have hMem : MemLp Z 2 P :=
    (avram_wave5_03a_actual_source_rightCont_stopped_gaussian_quotient_L2_centered
      X hν τ hτ T hbounded h θ hθ).1
  have hSq : Integrable (fun ω => (Z ω) ^ 2) P :=
    (memLp_two_iff_integrable_sq hMem.aestronglyMeasurable).mp hMem
  have hTop : Integrable (fun ω => K ^ 2 * (Z ω) ^ 2) P :=
    hSq.const_mul (K ^ 2)
  have hpoint (ω : Ω) : (H ω * Z ω) ^ 2 ≤ K ^ 2 * (Z ω) ^ 2 := by
    have hHa := abs_le.mp (hH ω)
    have hHs : (H ω) ^ 2 ≤ K ^ 2 := by
      have hp : 0 ≤ (K - H ω) * (K + H ω) :=
        mul_nonneg (sub_nonneg.mpr hHa.2) (by linarith)
      nlinarith
    calc
      _ = (H ω) ^ 2 * (Z ω) ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hHs (sq_nonneg _)
  have hE : (∫ ω, (Z ω) ^ 2 ∂P) =
      (Real.exp ((h : ℝ) * (X.σ ^ 2 * θ * θ)) - 1) / (θ * θ) := by
    simpa only [pow_two] using
      (avram_wave5_03a_actual_source_rightCont_stopped_gaussian_cross_quotient
        X hν τ hτ T hbounded h θ θ hθ hθ)
  calc
    (∫ ω, (H ω * Z ω) ^ 2 ∂P) ≤
        (∫ ω, K ^ 2 * (Z ω) ^ 2 ∂P) := by
      exact integral_mono_of_nonneg
        (Filter.Eventually.of_forall (fun ω => sq_nonneg _))
        hTop (Filter.Eventually.of_forall hpoint)
    _ = K ^ 2 * (∫ ω, (Z ω) ^ 2 ∂P) := by
      rw [integral_const_mul]
    _ = _ := by rw [hE]
