-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_negative_Borel_mark_simple_mean_of_separated_P2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:32:00.597902+00:00
-- url     : https://prove2.me/submissions/3a40bd1f-8966-4bad-8650-b4b43444a4f4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_P2_negative_Borel_rate_from_separated_bands
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_P2_mark_simple_raw_integral_mean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Original separated-band P2 rates suffice for the finite nonnegative
mark-simple physical first moment of the actual intrinsic jump measure. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {ι : Type*} (S : Finset ι) (s t : ℝ≥0)
    (B : ι → Set ℝ)
    (hB : ∀ i ∈ S, MeasurableSet (B i))
    (hNeg : ∀ i ∈ S, B i ⊆ Iio (0 : ℝ))
    (c : ι → ℝ≥0∞)
    (J : ι → Ω → ℝ≥0∞)
    (hJsource : ∀ i ω, J i ω =
      ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B i))
    (hJmeas : ∀ i ∈ S, Measurable (J i))
    (hCutMeas : ∀ i ∈ S, ∀ n : ℕ, Measurable (fun ω =>
        ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ (B i ∩ {z : ℝ |
            z < 0 ∧ (1 : ℝ) / ((n : ℝ) + 1) ≤ -z}))))
    (hCutRate : ∀ i ∈ S, ∀ n : ℕ, (∫⁻ ω,
        ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ (B i ∩ {z : ℝ |
            z < 0 ∧ (1 : ℝ) / ((n : ℝ) + 1) ≤ -z})) ∂P) =
        (((t - s : ℝ≥0) : ℝ≥0∞) *
          X.ν (B i ∩ {z : ℝ |
            z < 0 ∧ (1 : ℝ) / ((n : ℝ) + 1) ≤ -z}))) :
    (∫⁻ ω, (∫⁻ p : ℝ≥0 × ℝ,
      ∑ i ∈ S, (Ioc s t ×ˢ B i).indicator (fun _ => c i) p
      ∂((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) ∂P) =
    ∑ i ∈ S, c i * (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (B i)) := by
  let N : Ω → Measure (ℝ≥0 × ℝ) := fun ω => (Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
  have hN (ω : Ω) : N ω = (Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) := rfl
  have hRate : ∀ i ∈ S, (∫⁻ ω, J i ω ∂P) =
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (B i)) := by
    intro i hi
    calc
      _ = (∫⁻ ω, N ω (Ioc s t ×ˢ B i) ∂P) := by
        apply lintegral_congr_ae
        filter_upwards [] with ω
        exact hJsource i ω
      _ = _ := by
        apply avram_p4_b_smalljump_original_P2_negative_Borel_rate_from_separated_bands X N hN s t (B i) (hNeg i hi)
        · intro n; exact hCutMeas i hi n
        · intro n; exact hCutRate i hi n
  exact avram_p4_b_smalljump_original_P2_mark_simple_raw_integral_mean
    X S s t B hB c J hJsource hJmeas hRate
