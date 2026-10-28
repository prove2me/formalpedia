-- Prove2me | solution 1 for D1Bound5.pairSelectedFloorRowBool_sound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:35:02.406953+00:00
-- url     : https://prove2.me/submissions/383d5ed1-bf3e-42a8-bbda-d18a6ad22ca3

import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_PairCachedResidues_Definitions
import Definitions.Def_D1Bound5_PairNegativeIntegerObstruction_Definitions
import Definitions.Def_D1Bound5_PairSelectedCachedMask_Definitions
import Definitions.Def_D1Bound5_PairSelectedFloorWitnesses_Definitions
import Definitions.Def_D1Bound5_QuadSquareFloorObstruction_Definitions
import Definitions.Def_D1Bound5_SquareTest_Definitions
import Theorems.Thm_D1Bound5_QuadInt_floorObstructionBool_sound
import Theorems.Thm_D1Bound5_pairCachedHasSquareRoot_eq_false_of_no_root
import Theorems.Thm_D1Bound5_pairNegativeIntegerObstructionBool_sound
import Theorems.Thm_D1Bound5_pairSelectedCachedMaskRejectBool_sound

section
namespace D1Bound5
open QuadInt



/-- Every accepted tag rejects the exact cached pair test or checks an
actual repeated vertex. Thus all pairs in the entire tail are covered. -/
theorem _root_.solution {tau nu : ℤ}
    (hd : 0 < discriminant tau nu) (sieve : List (ℕ × ℕ))
    (x : PairResidueVertex tau nu) (ys : List (PairResidueVertex tau nu))
    (code : ℕ) (ks : List ℕ)
    (hcheck : pairSelectedFloorRowBool sieve x ys code ks = true) :
    (ys.all fun y => if decide (x.vertex = y.vertex) then true
      else !(pairCachedHasSquareRoot sieve x y)) = true := by
  induction ys generalizing code ks with
  | nil => rfl
  | cons y ys ih =>
      by_cases hindex : code % 32 < 25
      · have hparts :
            pairSelectedCachedMaskRejectBool tau nu sieve x.signature y.signature
                (code % 32) = true ∧
              pairSelectedFloorRowBool sieve x ys (code / 32) ks = true :=
          Bool.and_eq_true_iff.mp (by
            simpa only [pairSelectedFloorRowBool, if_pos hindex] using hcheck)
        have hcache := pairSelectedCachedMaskRejectBool_sound tau nu sieve
          x.signature y.signature (code % 32) hparts.1
        have hpair : pairCachedHasSquareRoot sieve x y = false := by
          simp only [pairCachedHasSquareRoot, hcache, Bool.false_and]
        simpa [hpair] using ih (code / 32) ks hparts.2
      · by_cases hrepeated : code % 32 = 30
        · have hparts : decide (x.vertex = y.vertex) = true ∧
                pairSelectedFloorRowBool sieve x ys (code / 32) ks = true :=
            Bool.and_eq_true_iff.mp (by
              simpa only [pairSelectedFloorRowBool, if_neg hindex,
                if_pos hrepeated] using hcheck)
          have heq : x.vertex = y.vertex := of_decide_eq_true hparts.1
          simpa [heq] using ih (code / 32) ks hparts.2
        · by_cases hfallback : code % 32 = 31
          · by_cases hobs : pairNegativeIntegerObstructionBool (x.vertex * y.vertex + 1) = true
            · have htail : pairSelectedFloorRowBool sieve x ys (code / 32) ks = true := by
                simpa only [pairSelectedFloorRowBool, if_neg hindex,
                  if_neg hrepeated, if_pos hfallback, if_pos hobs] using hcheck
              have hpair := pairCachedHasSquareRoot_eq_false_of_no_root hd sieve x y
                (pairNegativeIntegerObstructionBool_sound _ hobs)
              simpa [hpair] using ih (code / 32) ks htail
            · cases ks with
              | nil =>
                  simp only [pairSelectedFloorRowBool, if_neg hindex,
                    if_neg hrepeated, if_pos hfallback, if_neg hobs,
                    Bool.false_eq_true] at hcheck
              | cons k rest =>
                  have hparts : QuadInt.floorObstructionBool (x.vertex * y.vertex + 1) k = true ∧
                      pairSelectedFloorRowBool sieve x ys (code / 32) rest = true :=
                    Bool.and_eq_true_iff.mp (by
                      simpa only [pairSelectedFloorRowBool, if_neg hindex,
                        if_neg hrepeated, if_pos hfallback, if_neg hobs] using hcheck)
                  have hpair := pairCachedHasSquareRoot_eq_false_of_no_root hd sieve x y
                    (QuadInt.floorObstructionBool_sound hd hparts.1)
                  simpa [hpair] using ih (code / 32) rest hparts.2
          · simp only [pairSelectedFloorRowBool, if_neg hindex,
              if_neg hrepeated, if_neg hfallback, Bool.false_eq_true] at hcheck











end D1Bound5
end
