-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_multiplier_L2_cauchy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:21:56.625193+00:00
-- url     : https://prove2.me/submissions/c1812d25-8c9b-4c02-bf96-2f9396fde02b

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_original_rightCont_gaussian_quotient_two_sequence_L2_cauchy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_source_rightCont_stopped_gaussian_quotient_L2_centered

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false

/-- Same-source rightCont stopped Gaussian L2 Cauchy under a bounded multiplier. -/
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
    (θ η : ℕ → ℝ)
    (hθ : Filter.Tendsto θ atTop (𝓝[>] (0 : ℝ)))
    (hη : Filter.Tendsto η atTop (𝓝[>] (0 : ℝ))) :
    let Z : ℝ → Ω → ℝ := fun ξ ω =>
      (Real.exp (ξ * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
        (h : ℝ) * X.ψ ξ) - 1) / ξ
    Filter.Tendsto (fun n : ℕ =>
      (∫ ω, (H ω * (Z (θ n) ω - Z (η n) ω)) ^ 2 ∂P))
      atTop (𝓝 (0 : ℝ)) := by
  dsimp only
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let Z : ℝ → Ω → ℝ := fun ξ ω =>
    (Real.exp (ξ * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
      (h : ℝ) * X.ψ ξ) - 1) / ξ
  change Filter.Tendsto (fun n : ℕ =>
    (∫ ω, (H ω * (Z (θ n) ω - Z (η n) ω)) ^ 2 ∂P))
    atTop (𝓝 (0 : ℝ))
  have hθpos : ∀ᶠ n : ℕ in atTop, 0 < θ n :=
    hθ.eventually self_mem_nhdsWithin
  have hηpos : ∀ᶠ n : ℕ in atTop, 0 < η n :=
    hη.eventually self_mem_nhdsWithin
  have hCauchy : Filter.Tendsto (fun n : ℕ =>
      (∫ ω, (Z (θ n) ω - Z (η n) ω) ^ 2 ∂P))
      atTop (𝓝 (0 : ℝ)) :=
    avram_wave5_03a_original_rightCont_gaussian_quotient_two_sequence_L2_cauchy
      X hν τ hτ T hbounded h θ η hθ hη
  have hscale : Filter.Tendsto (fun n : ℕ =>
      K ^ 2 * (∫ ω, (Z (θ n) ω - Z (η n) ω) ^ 2 ∂P))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hCauchy.const_mul (K ^ 2)
  have hnonneg : ∀ n : ℕ,
      0 ≤ (∫ ω, (H ω * (Z (θ n) ω - Z (η n) ω)) ^ 2 ∂P) := by
    intro n
    exact integral_nonneg (fun ω => sq_nonneg _)
  have hupper : ∀ᶠ n : ℕ in atTop,
      (∫ ω, (H ω * (Z (θ n) ω - Z (η n) ω)) ^ 2 ∂P) ≤
        K ^ 2 * (∫ ω, (Z (θ n) ω - Z (η n) ω) ^ 2 ∂P) := by
    filter_upwards [hθpos, hηpos] with n hn hm
    have hMemθ : MemLp (Z (θ n)) 2 P :=
      (avram_wave5_03a_actual_source_rightCont_stopped_gaussian_quotient_L2_centered
        X hν τ hτ T hbounded h (θ n) (le_of_lt hn)).1
    have hMemη : MemLp (Z (η n)) 2 P :=
      (avram_wave5_03a_actual_source_rightCont_stopped_gaussian_quotient_L2_centered
        X hν τ hτ T hbounded h (η n) (le_of_lt hm)).1
    have hMemΔ : MemLp (fun ω => Z (θ n) ω - Z (η n) ω) 2 P :=
      hMemθ.sub hMemη
    have hSq : Integrable
        (fun ω => (Z (θ n) ω - Z (η n) ω) ^ 2) P :=
      (memLp_two_iff_integrable_sq hMemΔ.aestronglyMeasurable).mp hMemΔ
    have hTop : Integrable
        (fun ω => K ^ 2 * (Z (θ n) ω - Z (η n) ω) ^ 2) P :=
      hSq.const_mul (K ^ 2)
    have hpoint (ω : Ω) :
        (H ω * (Z (θ n) ω - Z (η n) ω)) ^ 2 ≤
        K ^ 2 * (Z (θ n) ω - Z (η n) ω) ^ 2 := by
      have hHa := abs_le.mp (hH ω)
      have hsq : (H ω) ^ 2 ≤ K ^ 2 := by
        have hp : 0 ≤ (K - H ω) * (K + H ω) :=
          mul_nonneg (sub_nonneg.mpr hHa.2) (by linarith)
        nlinarith
      calc
        _ = (H ω) ^ 2 * (Z (θ n) ω - Z (η n) ω) ^ 2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    calc
      (∫ ω, (H ω * (Z (θ n) ω - Z (η n) ω)) ^ 2 ∂P) ≤
          (∫ ω, K ^ 2 * (Z (θ n) ω - Z (η n) ω) ^ 2 ∂P) := by
        exact integral_mono_of_nonneg
          (Filter.Eventually.of_forall (fun ω => sq_nonneg _))
          hTop
          (Filter.Eventually.of_forall hpoint)
      _ = K ^ 2 * (∫ ω, (Z (θ n) ω - Z (η n) ω) ^ 2 ∂P) := by
        rw [integral_const_mul]
  exact squeeze_zero' (Filter.Eventually.of_forall hnonneg) hupper hscale
