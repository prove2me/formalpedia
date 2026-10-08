-- Prove2me | solution 4 for AvramDividend.Classical.scaleDeriv_continuous
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T15:13:31.563276+00:00
-- url     : https://prove2.me/submissions/23c9a3c3-d3db-43a9-a81f-654c99470745
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_excursion_tail_derivative_representation
import Theorems.Thm_AvramDividend_Classical_continuous_deriv_of_const_add_atomless_pos_tail_factor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Direct excursion-route proof of derivative continuity, avoiding the
broader ContDiffOn theorem on the Proposition 3(i) critical path. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ContinuousOn (deriv W) (Ioi 0) := by
  obtain ⟨φ, μ, hφ, hnull, hfin, hdiff, hrepr⟩ :=
    scaleFunction_excursion_tail_derivative_representation
      X hX q hq W hW
  letI : NullSingletonClass μ := hnull
  have hWcont : ContinuousOn W (Ioi (0 : ℝ)) := by
    apply hW.2.2.1.mono
    intro x hx
    have hxpos : 0 < x := by
      simpa only [Set.mem_Ioi] using hx
    exact hxpos.le
  exact continuous_deriv_of_const_add_atomless_pos_tail_factor
    μ hfin φ W hWcont hrepr
