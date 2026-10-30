-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_03_upper_endpoint_of_interior
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T08:10:17.706001+00:00
-- url     : https://prove2.me/submissions/bffb8d46-c981-415d-a34a-ce5b63e30e28

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_discounted_strict_exit_monotone_initial_reserve
import Theorems.Thm_AvramDividend_Classical_chat04_twoSidedExitExpectation_le_one
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- The upper endpoint follows from interior ratios by continuity and
monotonicity, with no upward-regularity premise. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (hInterior : ∀ y : ℝ, 0 < y → y < a →
      twoSidedExitExpectation X q a y = ENNReal.ofReal (W y / W a)) :
    twoSidedExitExpectation X q a a = ENNReal.ofReal (W a / W a) := by
  have hWa : W a ≠ 0 :=
    ne_of_gt (scaleFunction_strict_pos_of_standing X hX q hq W hW a ha)
  have hWcont : ContinuousAt W a :=
    hW.2.2.1.continuousAt (Ici_mem_nhds ha)
  have hQcont : ContinuousAt (fun y : ℝ => W y / W a) a :=
    hWcont.div continuousAt_const hWa
  have hRcont :
      ContinuousAt (fun y : ℝ => ENNReal.ofReal (W y / W a)) a :=
    ENNReal.continuous_ofReal.continuousAt.comp hQcont
  have hLimit :
      Tendsto (fun y : ℝ => ENNReal.ofReal (W y / W a))
        (𝓝[<] a) (𝓝 (ENNReal.ofReal (W a / W a))) :=
    hRcont.tendsto.mono_left nhdsWithin_le_nhds
  have hPositive : ∀ᶠ y : ℝ in 𝓝[<] a, 0 < y := by
    exact eventually_nhdsWithin_of_eventually_nhds (Ioi_mem_nhds ha)
  have hBelow : ∀ᶠ y : ℝ in 𝓝[<] a, y < a :=
    self_mem_nhdsWithin
  have hBound :
      ∀ᶠ y : ℝ in 𝓝[<] a,
        ENNReal.ofReal (W y / W a) ≤ twoSidedExitExpectation X q a a := by
    filter_upwards [hPositive, hBelow] with y hy0 hya
    rw [← hInterior y hy0 hya]
    exact chat04_discounted_strict_exit_monotone_initial_reserve
      X q a y a (le_of_lt hq) (le_of_lt hya)
  have hLower :
      ENNReal.ofReal (W a / W a) ≤ twoSidedExitExpectation X q a a :=
    le_of_tendsto hLimit hBound
  have hOne : ENNReal.ofReal (W a / W a) = 1 := by
    simp [hWa]
  apply le_antisymm
  · simpa only [hOne] using
      (chat04_twoSidedExitExpectation_le_one X q a a (le_of_lt hq))
  · exact hLower
