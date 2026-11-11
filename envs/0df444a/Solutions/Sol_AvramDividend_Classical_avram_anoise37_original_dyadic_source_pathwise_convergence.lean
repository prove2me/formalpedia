-- Prove2me | solution 1 for AvramDividend.Classical.avram_anoise37_original_dyadic_source_pathwise_convergence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T14:18:05.4472+00:00
-- url     : https://prove2.me/submissions/919e7a27-ccfa-4986-bf6d-f26d430a5a4a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_anoise41_original_dyadic_physical_mark_count_convergence
import Theorems.Thm_AvramDividend_Classical_avram_anoise42_original_dyadic_levy_compensator_approx
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

/-- The original dyadic compensated noise limit is the difference of physical counts and source rates. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hInt : ∀ n : ℕ, ∀ T : ℝ≥0, Integrable
      (fun ω => avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω) P) :
    ∀ n : ℕ, ∀ s t : ℝ≥0, s ≤ t →
      let B : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))
      let C : ℕ → ℕ → Set ℝ := fun k i =>
        B ∩ Ioc (-1 + (i : ℝ) / (2 : ℝ) ^ k)
          (-1 + ((i : ℝ) + 1) / (2 : ℝ) ^ k)
      let J : ℕ → ℕ → Ω → ℝ≥0∞ := fun k i ω =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ C k i)
      let M : ℕ → Ω → ℝ := fun k ω =>
        ∑ i ∈ Finset.range (2 ^ k),
          (-1 + (i : ℝ) / (2 : ℝ) ^ k) *
            ((J k i ω).toReal -
              (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (C k i)).toReal)
      (∀ᵐ ω ∂P, Tendsto (fun k => M k ω) atTop
        (𝓝 (avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω -
          avram_p4_h_gaussian_intrinsic_small_band_compensated X n s ω))) := by
  intro n s t hst
  have hCount :=
    avram_anoise41_original_dyadic_physical_mark_count_convergence X hFinite hInt n s t hst
  have hRate :=
    avram_anoise42_original_dyadic_levy_compensator_approx X hFinite hInt n s t hst
  filter_upwards [hCount] with ω hw
  have h := hw.sub hRate
  simpa only [mul_sub, Finset.sum_sub_distrib, add_sub_cancel_right]
    using h
