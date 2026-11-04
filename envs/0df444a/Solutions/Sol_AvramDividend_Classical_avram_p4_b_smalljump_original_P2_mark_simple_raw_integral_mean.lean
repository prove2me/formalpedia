-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_P2_mark_simple_raw_integral_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:44:54.96039+00:00
-- url     : https://prove2.me/submissions/54c41cf5-2ea2-441c-b9cd-41af7bf1a6ff

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_intrinsic_nonnegative_mark_simple_lintegral

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Under original source P2 first-moment rates, the actual raw marked
simple-jump integral has the finite weighted original Lévy rate mean. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {ι : Type*} (S : Finset ι) (s t : ℝ≥0)
    (B : ι → Set ℝ) (hB : ∀ i ∈ S, MeasurableSet (B i))
    (c : ι → ℝ≥0∞) (J : ι → Ω → ℝ≥0∞)
    (hJsource : ∀ i ω, J i ω =
      ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B i))
    (hJmeas : ∀ i ∈ S, Measurable (J i))
    (hRate : ∀ i ∈ S, (∫⁻ ω, J i ω ∂P) =
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (B i))) :
    (∫⁻ ω, (∫⁻ p : ℝ≥0 × ℝ,
      ∑ i ∈ S, (Ioc s t ×ˢ B i).indicator (fun _ => c i) p
      ∂((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) ∂P) =
    ∑ i ∈ S, c i * (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (B i)) := by
  calc
    _ = (∫⁻ ω, ∑ i ∈ S, c i * J i ω ∂P) := by
      apply lintegral_congr_ae
      filter_upwards [] with ω
      rw [avram_p4_b_smalljump_original_intrinsic_nonnegative_mark_simple_lintegral
        X S s t B hB c ω]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hJsource i ω]
    _ = ∑ i ∈ S, (∫⁻ ω, c i * J i ω ∂P) := by
      rw [lintegral_finset_sum S]
      intro i hi
      exact measurable_const.mul (hJmeas i hi)
    _ = ∑ i ∈ S, c i * (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (B i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [lintegral_const_mul (c i) (hJmeas i hi), hRate i hi]
