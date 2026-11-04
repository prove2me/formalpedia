-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_original_compact_negative_test_real_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:06:50.531449+00:00
-- url     : https://prove2.me/submissions/e89df80f-93ba-4b32-b1c0-03db505b7c4e

import Mathlib.Topology.Algebra.Order.Field
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_compact_negative_support_has_band
import Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_original_negative_compact_test_real_rate
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal

/-- A compact strictly negative test has its original source marginal Lévy rate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (g : ℝ → ℝ) (hg : Continuous g)
    (hc : IsCompact (tsupport g))
    (hneg : tsupport g ⊆ Iio (0 : ℝ)) :
    Tendsto (fun h : ℝ =>
      (∫ ω, g (X.X (Real.toNNReal h) ω) ∂P) / h)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (∫ y : ℝ, g y ∂(X.ν.restrict (Iio (0 : ℝ))))) := by
  obtain ⟨a, ε, hε, hlower, hupper⟩ :=
    avram_p2_j_ui_compact_negative_support_has_band g hc hneg
  have hRate := avram_p2_i_moment_original_negative_compact_test_real_rate
    X g hg a ε hε hlower hupper
  have hEq :
      (fun h : ℝ => if 0 < h then
        h⁻¹ * (∫ ω, g (X.X (Real.toNNReal h) ω) ∂P) else 0) =ᶠ[
          nhdsWithin (0 : ℝ) (Ioi 0)]
      (fun h : ℝ => (∫ ω, g (X.X (Real.toNNReal h) ω) ∂P) / h) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh' : 0 < h := hh
    simp [hh', div_eq_mul_inv, mul_comm]
  exact hRate.congr' hEq
