-- Prove2me | solution 1 for AvramDividend.Classical.avram_b20_original_countable_reciprocal_mark_levels_null
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T20:55:19.17743+00:00
-- url     : https://prove2.me/submissions/d099dfe8-21d9-44d4-a9d5-abbb5648df8a

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja34_original_all_negative_borel_expected_count_exact
import Theorems.Thm_AvramDividend_Classical_levyMeasure_singleton_null_of_standing_boundedVariation
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_rectangle_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P,
      ((Measure.count.restrict {t : ℝ≥0 |
          0 < t ∧ X.X t ω -
            Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t, X.X t ω -
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)))
        (⋃ p : ℕ × ℕ, Ioc (0 : ℝ≥0) (p.1 : ℝ≥0) ×ˢ
          ({-(1 / ((p.2 : ℝ) + 1))} : Set ℝ)) = 0 := by
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {t : ℝ≥0 |
        0 < t ∧ X.X t ω -
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0}).map
      (fun t : ℝ≥0 => (t, X.X t ω -
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)))
  let B : ℕ × ℕ → Set ℝ := fun p =>
    {-(1 / ((p.2 : ℝ) + 1))}
  let A : ℕ × ℕ → Set (ℝ≥0 × ℝ) := fun p =>
    Ioc (0 : ℝ≥0) (p.1 : ℝ≥0) ×ˢ B p
  have hOrigin (p : ℕ × ℕ) : (∫⁻ ω, NX ω (A p) ∂P) = 0 := by
    have hNeg : B p ⊆ Iio (0 : ℝ) := by
      intro z hz
      change z = -(1 / ((p.2 : ℝ) + 1)) at hz
      subst z
      have hp : 0 < (p.2 : ℝ) + 1 := by positivity
      exact neg_lt_zero.mpr (one_div_pos.mpr hp)
    have hRate := avram_ja34_original_all_negative_borel_expected_count_exact
      X (p.1 : ℝ≥0) (B p) (measurableSet_singleton _) hNeg
    have hν : X.ν (B p) = 0 :=
      levyMeasure_singleton_null_of_standing_boundedVariation
        X hX hBV _
    change (∫⁻ ω, NX ω (A p) ∂P) =
      (p.1 : ℝ≥0∞) * X.ν (B p) at hRate
    simpa only [hν, mul_zero] using hRate
  have hMeas (p : ℕ × ℕ) : Measurable (fun ω => NX ω (A p)) := by
    simpa only [zero_add] using
      (avram_p2_f_weighted_original_intrinsic_rectangle_measurable
        X 0 (p.1 : ℝ≥0) (B p) (measurableSet_singleton _))
  have hAE (p : ℕ × ℕ) : ∀ᵐ ω ∂P, NX ω (A p) = 0 :=
    (lintegral_eq_zero_iff (hMeas p)).mp (hOrigin p)
  have hAll : ∀ᵐ ω ∂P, ∀ p : ℕ × ℕ, NX ω (A p) = 0 :=
    ae_all_iff.mpr hAE
  filter_upwards [hAll] with ω hω
  change NX ω (⋃ p : ℕ × ℕ, A p) = 0
  exact measure_iUnion_null hω
