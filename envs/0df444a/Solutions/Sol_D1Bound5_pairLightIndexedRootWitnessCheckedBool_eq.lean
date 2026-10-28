-- Prove2me | solution 1 for D1Bound5.pairLightIndexedRootWitnessCheckedBool_eq
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:34:53.698058+00:00
-- url     : https://prove2.me/submissions/4998b91d-b824-4ea6-8f43-9691a38e1006

import Init
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
import Definitions.Def_D1Bound5_DescentAlgebra_Definitions
import Definitions.Def_D1Bound5_PairClosureIndexedWitness_Definitions
import Definitions.Def_D1Bound5_PairClosureWitness_Definitions
import Definitions.Def_D1Bound5_PairLightArithmeticBridge_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_PairLightClosureBridge_Definitions
import Definitions.Def_D1Bound5_PairLightClosure_Definitions
import Theorems.Thm_D1Bound5_pairLightCoordinates_eq_iff
import Theorems.Thm_D1Bound5_pairLightIndexedCandidateCoveredBool_eq
import Theorems.Thm_D1Bound5_pairLightProductPlusOne_eq

section
namespace D1Bound5



theorem pairLightMul_eq {tau nu : ℤ} (x y : QuadInt tau nu) :
    pairLightMul tau nu (pairLightCoordinates x) (pairLightCoordinates y) =
      pairLightCoordinates (x * y) := by
  apply Prod.ext <;>
    simp only [pairLightMul, pairLightCoordinates,
      QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul] <;> ring

theorem pairLightNeg_eq {tau nu : ℤ} (x : QuadInt tau nu) :
    pairLightNeg (pairLightCoordinates x) = pairLightCoordinates (-x) := by
  rfl

theorem pairLightMutate_eq {tau nu : ℤ} (a b z r0 r s : QuadInt tau nu) :
    pairLightMutate tau nu (pairLightCoordinates a) (pairLightCoordinates b)
      (pairLightCoordinates z) (pairLightCoordinates r0) (pairLightCoordinates r)
      (pairLightCoordinates s) = pairLightCoordinates (mutate a b z r0 r s) := by
  apply Prod.ext <;>
    simp only [pairLightMutate, pairLightAdd, pairLightMul, pairLightCoordinates, mutate,
      QuadraticAlgebra.re_add, QuadraticAlgebra.im_add,
      QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
      QuadraticAlgebra.re_one, QuadraticAlgebra.im_one,
      QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat] <;> ring



theorem _root_.solution {tau nu : ℤ}
    (a b r0 : QuadInt tau nu) (bound : ℤ) (vertices : List (QuadInt tau nu))
    (w : PairRootWitness tau nu) (destinations : Option Nat × Option Nat) :
    pairLightIndexedRootWitnessCheckedBool tau nu
      (pairLightCoordinates a) (pairLightCoordinates b) (pairLightCoordinates r0) bound
      (vertices.map pairLightCoordinates) (pairLightRootWitnessCoordinates w) destinations =
      pairIndexedRootWitnessCheckedBool a b r0 bound vertices w destinations := by
  simp only [pairLightIndexedRootWitnessCheckedBool, pairIndexedRootWitnessCheckedBool,
    pairLightRootWitnessCoordinates, pairLightMul_eq, pairLightProductPlusOne_eq,
    pairLightCoordinates_eq_iff, pairLightNeg_eq, pairLightMutate_eq,
    pairLightIndexedCandidateCoveredBool_eq]



end D1Bound5
end
