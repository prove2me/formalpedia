-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_jump8_turn12_intrinsic_weighted_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T12:28:33.240117+00:00
-- url     : https://prove2.me/submissions/ec6faccb-22ea-4e60-b0e1-be4a3eb7de4a

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_redux20_original_strict_marked_borel_weight_finite_sum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Rewrite the genuine intrinsic original marked integral under a time-space
restriction as its already-Proved unrestricted Borel-weighted finite sum. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (k n : ℕ) :
    let T : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
    let ε : ℝ := 1 / ((k : ℝ) + 1)
    let φ : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal (1 - Real.exp y)
    let B : Set ℝ := Iio (-ε)
    let S : Ω → Finset ℝ≥0 := fun ω =>
      (avram_redux19_original_strict_negative_marked_times_finite X ω T k).toFinset
    ∀ ω : Ω,
      (∫⁻ p in (Ioc 0 T ×ˢ (univ : Set ℝ)),
        (B.indicator φ) p.2 ∂((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) =
      ∑ u ∈ S ω, ENNReal.ofReal
        (1 - Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) := by
  let T : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
  let ε : ℝ := 1 / ((k : ℝ) + 1)
  let φ : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal (1 - Real.exp y)
  let B : Set ℝ := Iio (-ε)
  let S : Ω → Finset ℝ≥0 := fun ω =>
    (avram_redux19_original_strict_negative_marked_times_finite X ω T k).toFinset
  change ∀ ω : Ω,
    (∫⁻ p in (Ioc 0 T ×ˢ (univ : Set ℝ)),
      (B.indicator φ) p.2 ∂((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) =
    ∑ u ∈ S ω, φ (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
  intro ω
  let μ : Measure (ℝ≥0 × ℝ) :=
    (Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
  have hφ : Measurable φ := by
    dsimp [φ]
    fun_prop
  have hfull : (∫⁻ p : ℝ≥0 × ℝ,
      if 0 < p.1 ∧ p.1 ≤ T ∧ p.2 < -ε then φ p.2 else 0 ∂μ) =
      ∑ u ∈ S ω, φ (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) := by
    simpa only [T, ε, φ, S, μ] using
      (avram_redux20_original_strict_marked_borel_weight_finite_sum
        X ω T k φ hφ)
  have hm : MeasurableSet (Ioc 0 T ×ˢ (univ : Set ℝ)) :=
    measurableSet_Ioc.prod MeasurableSet.univ
  have hrewrite :
      (∫⁻ p in (Ioc 0 T ×ˢ (univ : Set ℝ)), (B.indicator φ) p.2 ∂μ) =
      (∫⁻ p, if 0 < p.1 ∧ p.1 ≤ T ∧ p.2 < -ε then φ p.2 else 0 ∂μ) := by
    rw [← lintegral_indicator hm]
    apply lintegral_congr
    intro p
    by_cases ht1 : 0 < p.1
    · by_cases ht2 : p.1 ≤ T
      · by_cases hb : p.2 < -ε
        · simp [Set.indicator, Set.mem_prod, B, ht1, ht2, hb]
        · simp [Set.indicator, Set.mem_prod, B, ht1, ht2, hb]
      · simp [Set.indicator, Set.mem_prod, B, ht1, ht2]
    · simp [Set.indicator, Set.mem_prod, B, ht1]
  exact hrewrite.trans hfull
