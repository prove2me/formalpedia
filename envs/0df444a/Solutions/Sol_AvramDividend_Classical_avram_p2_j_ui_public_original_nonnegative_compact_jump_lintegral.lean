-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_public_original_nonnegative_compact_jump_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T01:10:51.327942+00:00
-- url     : https://prove2.me/submissions/5da738ad-5b6c-44fd-b52f-572a2611c544

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_public_original_uncentered_compact_jump_mean
import Mathlib.Topology.Order.LeftRightLim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The public original compact-test intrinsic jump first moment has its ENNReal form. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (f : ℝ → ℝ) (hf : Continuous f)
    (hc : IsCompact (tsupport f)) (hneg : tsupport f ⊆ Iio (0 : ℝ))
    (a ε : ℝ) (hε : 0 < ε)
    (hflower : ∀ y : ℝ, y < a → f y = 0)
    (hfupper : ∀ y : ℝ, -ε < y → f y = 0)
    (hXm : ∀ t : ℝ≥0, Measurable (X.X t))
    (T : ℝ≥0) (hT : 0 < T)
    (hfnonneg : ∀ y : ℝ, 0 ≤ f y) :
    ∃ J : Ω → ℝ, Integrable J P ∧
      (∀ ω, ∃ F : Finset ℝ≥0,
        (∀ u : ℝ≥0, u ∈ F ↔ 0 < u ∧ u ≤ T ∧
          f (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) ≠ 0) ∧
        J ω = ∑ u ∈ F,
          f (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) ∧
      (∀ ω, 0 ≤ J ω) ∧
      (∫⁻ ω, ENNReal.ofReal (J ω) ∂P) =
        ENNReal.ofReal ((T : ℝ) *
          (∫ y : ℝ, f y ∂(X.ν.restrict (Iio (0 : ℝ))))) := by
  obtain ⟨J, hJInt, hRep, hMean⟩ :=
    avram_p2_j_ui_public_original_uncentered_compact_jump_mean
      P X f hf hc hneg a ε hε hflower hfupper hXm T hT
  have hJNonneg : ∀ ω, 0 ≤ J ω := by
    intro ω
    obtain ⟨F, _, hJ⟩ := hRep ω
    rw [hJ]
    exact Finset.sum_nonneg (fun u _ => hfnonneg _)
  refine ⟨J, hJInt, hRep, hJNonneg, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hJInt
    (Filter.Eventually.of_forall hJNonneg), hMean]
