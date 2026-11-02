-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_01_actual_source_jumpmark_vanish_from_right
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:50:08.293671+00:00
-- url     : https://prove2.me/submissions/53f47131-81dd-4721-b417-548b1c003c19

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- A real source Levy path has vanishing true jump marks at times tending
down to any fixed observation clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (t : ℝ≥0) :
    Tendsto
      (fun u : ℝ≥0 =>
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
      (𝓝[>] t) (𝓝 (0 : ℝ)) := by
  let f : ℝ≥0 → ℝ := fun u => X.X u ω
  let g : ℝ≥0 → ℝ := Function.leftLim f
  have hright : Tendsto f (𝓝[>] t) (𝓝 (f t)) :=
    (X.rightCont ω t).mono_left
      (nhdsWithin_mono t Set.Ioi_subset_Ici_self)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let r : ℝ := ε / 3
  have hr : 0 < r := by dsimp [r]; linarith
  have hev : ∀ᶠ u in 𝓝[>] t, dist (f u) (f t) < r := by
    exact hright.eventually (Metric.ball_mem_nhds (f t) hr)
  obtain ⟨b, hb, hcover⟩ := (nhdsGT_basis t).mem_iff.mp hev
  apply (nhdsGT_basis t).mem_iff.mpr
  refine ⟨b, hb, ?_⟩
  intro u hu
  have hu_pos : 0 < u := lt_of_le_of_lt (zero_le : (0 : ℝ≥0) ≤ t) hu.1
  have hleft :
      Tendsto f (𝓝[<] u) (𝓝 (g u)) := by
    exact tendsto_leftLim_of_tendsto (X.leftLim ω u hu_pos)
  haveI : (𝓝[<] u).NeBot := nhdsLT_neBot_of_exists_lt ⟨t, hu.1⟩
  have hnear :
      ∀ᶠ v in 𝓝[<] u, f v ∈ Metric.closedBall (f t) r := by
    filter_upwards [Ioo_mem_nhdsLT hu.1] with v hv
    apply Metric.mem_closedBall.mpr
    exact le_of_lt (hcover ⟨hv.1, lt_trans hv.2 hu.2⟩)
  have hgu : dist (g u) (f t) ≤ r :=
    Metric.mem_closedBall.mp
      (Metric.isClosed_closedBall.mem_of_tendsto hleft hnear)
  have hfu : dist (f u) (f t) < r := hcover hu
  have htri : dist (f u) (g u) ≤ dist (f u) (f t) + dist (f t) (g u) :=
    dist_triangle _ _ _
  have htwo : dist (f u) (g u) < r + r := by
    calc
      dist (f u) (g u) ≤ dist (f u) (f t) + dist (f t) (g u) := htri
      _ < r + r := add_lt_add_of_lt_of_le hfu (by simpa [dist_comm] using hgu)
  have hsmall : r + r < ε := by dsimp [r]; linarith
  change dist (f u - g u) 0 < ε
  simpa [Real.dist_eq] using lt_trans htwo hsmall
