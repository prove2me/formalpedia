-- Prove2me | solution 1 for BookProof.WeakSecondDeriv.absolutelyContinuous_primitive
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T17:21:07.691846+00:00
-- url     : https://prove2.me/submissions/b49051ba-a735-421a-a531-f4b9e0ca6269

-- Generated from ChapterWeakSecondDerivative.lean — solution of BookProof.WeakSecondDeriv.absolutelyContinuous_primitive
import Mathlib
import Definitions.Def_ChapterWeakSecondDerivative
open BookProof.WeakSecondDeriv




open MeasureTheory Filter Topology intervalIntegral Set

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution {G : ℝ → ℝ} (hG : LocallyIntegrable G volume)
    {a b c : ℝ} (hc : c ∈ uIcc a b) :
    AbsolutelyContinuousOnInterval (fun x => ∫ t in c..x, G t) a b :=
  IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral
      (hG.integrableOn_isCompact isCompact_uIcc).intervalIntegrable hc
