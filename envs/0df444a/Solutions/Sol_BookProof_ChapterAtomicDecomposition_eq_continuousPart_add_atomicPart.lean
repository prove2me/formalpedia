-- Prove2me | solution 1 for BookProof.ChapterAtomicDecomposition.eq_continuousPart_add_atomicPart
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T06:04:29.912972+00:00
-- url     : https://prove2.me/submissions/23586da7-8374-4eab-b932-5cefa36b85f5

-- Generated from ChapterAtomicDecomposition.lean — theorem BookProof.ChapterAtomicDecomposition.eq_continuousPart_add_atomicPart
import Mathlib
import Definitions.Def_ChapterAtomicDecomposition
open BookProof.ChapterAtomicDecomposition


open MeasureTheory


variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]


theorem solution (mu : Measure X) [SFinite mu] :
    mu = continuousPart mu + atomicPart mu := by
  have hc : (atoms mu).Countable := by
    exact Measure.countable_meas_pos_of_disjoint_iUnion
      (fun x : X => measurableSet_singleton x)
      (fun x y hxy => Set.disjoint_singleton.mpr hxy)
  exact (Measure.restrict_compl_add_restrict hc.measurableSet).symm

#print axioms solution

