-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_P2_negative_Borel_rate_from_separated_bands
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:22:19.997954+00:00
-- url     : https://prove2.me/submissions/eda14623-848a-45da-af08-38e088c6b621

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_P2_monotone_mark_rate_extension

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Genuine source P2 rates on reciprocal-separated negative bands extend
to any original negative Borel mark set under physical P. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (N : Ω → Measure (ℝ≥0 × ℝ))
    (hN : ∀ ω, N ω =
      (Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    (s t : ℝ≥0) (B : Set ℝ) (hNeg : B ⊆ Iio (0 : ℝ))
    (hMeas : ∀ n : ℕ, Measurable (fun ω =>
      N ω (Ioc s t ×ˢ (B ∩ {z : ℝ |
        z < 0 ∧ (1 : ℝ) / ((n : ℝ) + 1) ≤ -z}))))
    (hRate : ∀ n : ℕ,
      (∫⁻ ω, N ω (Ioc s t ×ˢ (B ∩ {z : ℝ |
        z < 0 ∧ (1 : ℝ) / ((n : ℝ) + 1) ≤ -z})) ∂P) =
      (((t - s : ℝ≥0) : ℝ≥0∞) *
        X.ν (B ∩ {z : ℝ |
          z < 0 ∧ (1 : ℝ) / ((n : ℝ) + 1) ≤ -z}))) :
    (∫⁻ ω, N ω (Ioc s t ×ˢ B) ∂P) =
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) := by
  let C : ℕ → Set ℝ := fun n => B ∩
    {z : ℝ | z < 0 ∧ (1 : ℝ) / ((n : ℝ) + 1) ≤ -z}
  have hMon : Monotone C := by
    intro n m hnm z hz
    refine ⟨hz.1, hz.2.1, ?_⟩
    have hm : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by
      exact_mod_cast Nat.add_le_add_right hnm 1
    have hRec : (1 : ℝ) / ((m : ℝ) + 1) ≤
        1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) hm
    exact hRec.trans hz.2.2
  have hUnion : (⋃ n, C n) = B := by
    ext z
    simp only [mem_iUnion, mem_inter_iff, mem_setOf_eq]
    constructor
    · rintro ⟨n, hz, -⟩
      exact hz
    · intro hz
      have hzNeg : z < 0 := hNeg hz
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < -z by linarith)
      exact ⟨n, hz, hzNeg, le_of_lt hn⟩
  simpa only [hUnion] using
    (avram_p4_b_smalljump_original_P2_monotone_mark_rate_extension
      X N hN s t C hMon hMeas hRate)
