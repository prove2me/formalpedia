-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_03_controlled_no_positive_jumps
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T23:03:47.877382+00:00
-- url     : https://prove2.me/submissions/2ced5658-a489-4200-ab4d-cde390585b11

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set
open AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t) (l : ℝ)
    (hl : Tendsto (fun s : ℝ≥0 => riskProcess X x D s ω) (𝓝[<] t) (𝓝 l)) :
    riskProcess X x D t ω ≤ l := by
  have hDleft :
      Tendsto (fun s : ℝ≥0 => D s ω) (𝓝[<] t) (𝓝 (D t ω)) := by
    have hcont : ContinuousWithinAt (fun s : ℝ≥0 => D s ω) (Iio t) t :=
      (hD.2.2.1 ω t).mono (Iio_subset_Iic le_rfl)
    exact hcont.tendsto
  have hsum :
      Tendsto (fun s : ℝ≥0 => riskProcess X x D s ω + D s ω - x)
        (𝓝[<] t) (𝓝 ((l + D t ω) - x)) :=
    (hl.add hDleft).sub tendsto_const_nhds
  have hfun :
      (fun s : ℝ≥0 => riskProcess X x D s ω + D s ω - x) =
        (fun s : ℝ≥0 => X.X s ω) := by
    funext s
    simp only [riskProcess]
    ring
  have hlim : (l + D t ω) - x = l - x + D t ω := by ring
  rw [hfun, hlim] at hsum
  have hX := X.noPosJumps ω t (l - x + D t ω) ht hsum
  dsimp [riskProcess]
  linarith