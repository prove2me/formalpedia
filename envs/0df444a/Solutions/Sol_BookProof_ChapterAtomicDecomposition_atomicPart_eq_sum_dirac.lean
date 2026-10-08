-- Prove2me | solution 1 for BookProof.ChapterAtomicDecomposition.atomicPart_eq_sum_dirac
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T06:04:33.843839+00:00
-- url     : https://prove2.me/submissions/b88d93b5-ba53-45e5-a11f-c4a682bcb0c7

-- Generated from ChapterAtomicDecomposition.lean — theorem BookProof.ChapterAtomicDecomposition.atomicPart_eq_sum_dirac
import Mathlib
import Definitions.Def_ChapterAtomicDecomposition
open BookProof.ChapterAtomicDecomposition


open MeasureTheory


variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]


theorem solution (mu : Measure X) [SFinite mu] :
    atomicPart mu = Measure.sum (fun x : atoms mu => mu {(x : X)} • Measure.dirac (x : X)) := by
  have hc : (atoms mu).Countable := by
    exact Measure.countable_meas_pos_of_disjoint_iUnion
      (fun x : X => measurableSet_singleton x)
      (fun x y hxy => Set.disjoint_singleton.mpr hxy)
  have hu : (⋃ x : atoms mu, ({(x : X)} : Set X)) = atoms mu := by
    ext x
    simp
  letI : Countable (atoms mu) := hc.to_subtype
  calc
    atomicPart mu = mu.restrict (⋃ x : atoms mu, ({(x : X)} : Set X)) := by
      rw [hu]
      rfl
    _ = Measure.sum (fun x : atoms mu => mu.restrict {(x : X)}) :=
      Measure.restrict_iUnion
        (fun x y hxy => Set.disjoint_singleton.mpr (Subtype.coe_ne_coe.mpr hxy))
        (fun x => measurableSet_singleton (x : X))
    _ = _ := by
      congr 1
      funext x
      exact Measure.restrict_singleton mu (x : X)

#print axioms solution
