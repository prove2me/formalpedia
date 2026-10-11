-- Prove2me | solution 1 for BlackScholesModel.gaussianReal_halfline_probs
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T17:08:59.058987+00:00
-- url     : https://prove2.me/submissions/c33aca86-2432-43fb-a502-7f2263818e08

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Theorems.Thm_BlackScholesModel_gaussianReal_Iic_eq_stdNormalCDF
import Theorems.Thm_BlackScholesModel_stdNormalCDF_neg

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff ENNReal
open BlackScholesModel

/-- Standard Gaussian masses of the strictly upper and lower rays. -/
theorem solution (x : ℝ) :
    (gaussianReal 0 1).real (Set.Ioi x) = stdNormalCDF (-x) ∧
    (gaussianReal 0 1).real (Set.Iio x) = stdNormalCDF x := by
  letI : NullSingletonClass (gaussianReal 0 (1 : NNReal)) :=
    ProbabilityTheory.noAtoms_gaussianReal (by norm_num)
  have hbridge :
      (gaussianReal 0 (1 : NNReal)).real (Set.Iic x) =
        stdNormalCDF x := gaussianReal_Iic_eq_stdNormalCDF x
  constructor
  · calc
      (gaussianReal 0 (1 : NNReal)).real (Set.Ioi x) =
          (gaussianReal 0 (1 : NNReal)).real (Set.Iic x)ᶜ := by
            rw [Set.compl_Iic]
      _ = (gaussianReal 0 (1 : NNReal)).real Set.univ -
          (gaussianReal 0 (1 : NNReal)).real (Set.Iic x) :=
            MeasureTheory.measureReal_compl measurableSet_Iic
      _ = 1 - stdNormalCDF x := by rw [hbridge]; simp
      _ = stdNormalCDF (-x) := (stdNormalCDF_neg x).symm
  · have hsingleton :
        (gaussianReal 0 (1 : NNReal)).real ({x} : Set ℝ) = 0 := by
      change ((gaussianReal 0 (1 : NNReal)) ({x} : Set ℝ)).toReal = 0
      rw [MeasureTheory.NullSingletonClass.measure_singleton]
      rfl
    have hset : (Set.Iic x \ {x}) = Set.Iio x := by
      ext z
      simp only [Set.mem_diff, Set.mem_Iic, Set.mem_singleton_iff, Set.mem_Iio]
      constructor
      · rintro ⟨hle, hne⟩
        exact lt_of_le_of_ne hle hne
      · intro hlt
        exact ⟨le_of_lt hlt, ne_of_lt hlt⟩
    calc
      (gaussianReal 0 (1 : NNReal)).real (Set.Iio x) =
          (gaussianReal 0 (1 : NNReal)).real
            (Set.Iic x \ {x}) := by rw [hset]
      _ = (gaussianReal 0 (1 : NNReal)).real (Set.Iic x) :=
        MeasureTheory.measureReal_diff_null hsingleton
      _ = stdNormalCDF x := hbridge