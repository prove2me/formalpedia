-- Prove2me | solution 1 for BookProof.ChapterAtomicDecomposition.atoms_countable
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T06:04:23.042231+00:00
-- url     : https://prove2.me/submissions/b8089058-c4ad-4e1f-a3d7-9e305bc738cc

-- Generated from ChapterAtomicDecomposition.lean — theorem BookProof.ChapterAtomicDecomposition.atoms_countable
import Mathlib
import Definitions.Def_ChapterAtomicDecomposition
open BookProof.ChapterAtomicDecomposition


open MeasureTheory


variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]


theorem solution (mu : Measure X) [SFinite mu] : (atoms mu).Countable := by
  exact Measure.countable_meas_pos_of_disjoint_iUnion
    (fun x : X => measurableSet_singleton x)
    (fun x y hxy => Set.disjoint_singleton.mpr hxy)

#print axioms solution

