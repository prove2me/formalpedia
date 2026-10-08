-- Prove2me | solution 5 for AvramDividend.Classical.scaleDeriv_continuous
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T20:54:57.815692+00:00
-- url     : https://prove2.me/submissions/bbea1f9a-6cb4-4d6a-ab3b-2ed5befb24fb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_excursion_tail_derivative_representation
import Theorems.Thm_AvramDividend_Classical_continuousOn_measureReal_Ici_of_finite_pos_noAtoms

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Derivative continuity from the precise Esscher excursion-tail representation,
without passing through the broader C1 theorem. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ContinuousOn (deriv W) (Ioi 0) := by
  obtain ⟨φ, μ, hφ, hnull, hfin, hdiff, hrepr⟩ :=
    scaleFunction_excursion_tail_derivative_representation
      X hX q hq W hW
  letI : NullSingletonClass μ := hnull
  have htail :
      ContinuousOn (fun x : ℝ => μ.real (Ici x)) (Ioi 0) :=
    continuousOn_measureReal_Ici_of_finite_pos_noAtoms μ hfin
  have hsum :
      ContinuousOn (fun x : ℝ => φ + μ.real (Ici x)) (Ioi 0) :=
    continuousOn_const.add htail
  have hWcont : ContinuousOn W (Ioi 0) :=
    hW.2.2.1.mono (by
      intro x hx
      have hxpos : 0 < x := by simpa only [Set.mem_Ioi] using hx
      exact hxpos.le)
  have hprod :
      ContinuousOn (fun x : ℝ => W x * (φ + μ.real (Ici x))) (Ioi 0) :=
    hWcont.mul hsum
  exact hprod.congr (by
    intro x hx
    have hxpos : 0 < x := by simpa only [Set.mem_Ioi] using hx
    exact hrepr x hxpos)
