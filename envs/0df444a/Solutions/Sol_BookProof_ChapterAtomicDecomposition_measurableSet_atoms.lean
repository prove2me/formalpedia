-- Prove2me | solution 1 for BookProof.ChapterAtomicDecomposition.measurableSet_atoms
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T06:04:25.937878+00:00
-- url     : https://prove2.me/submissions/2062de03-4e57-4a16-8e68-8d1527c6e1a3

-- Generated from ChapterAtomicDecomposition.lean — theorem BookProof.ChapterAtomicDecomposition.measurableSet_atoms
import Mathlib
import Definitions.Def_ChapterAtomicDecomposition
open BookProof.ChapterAtomicDecomposition


open MeasureTheory


variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]


theorem solution (mu : Measure X) [SFinite mu] : MeasurableSet (atoms mu) := by
  have hc : (atoms mu).Countable := by
    exact Measure.countable_meas_pos_of_disjoint_iUnion
      (fun x : X => measurableSet_singleton x)
      (fun x y hxy => Set.disjoint_singleton.mpr hxy)
  exact hc.measurableSet

#print axioms solution

