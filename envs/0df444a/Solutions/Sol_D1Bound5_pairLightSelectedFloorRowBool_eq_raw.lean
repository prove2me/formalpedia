-- Prove2me | solution 1 for D1Bound5.pairLightSelectedFloorRowBool_eq_raw
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:36:07.648021+00:00
-- url     : https://prove2.me/submissions/7ef66ed9-8f64-4499-94a3-19bfa9131a1c

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
import Definitions.Def_D1Bound5_PairCachedResidues_Definitions
import Definitions.Def_D1Bound5_PairLightArithmeticBridge_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_PairNegativeIntegerObstruction_Definitions
import Definitions.Def_D1Bound5_PairRawSelectedFloorWitnesses_Definitions
import Definitions.Def_D1Bound5_QuadSquareFloorObstruction_Definitions
import Theorems.Thm_D1Bound5_QuadInt_norm_formula
import Theorems.Thm_D1Bound5_pairLightCoordinates_eq_iff
import Theorems.Thm_D1Bound5_pairLightProductPlusOne_eq
import Theorems.Thm_D1Bound5_pairLightSelectedMaskRejectBool_eq_raw

section
namespace D1Bound5

























theorem pairLightNegativeIntegerObstructionBool_eq {tau nu : ℤ} (z : QuadInt tau nu) :
    pairLightNegativeIntegerObstructionBool tau nu (pairLightCoordinates z) =
      pairNegativeIntegerObstructionBool z := by
  rfl

theorem pairLightFloorObstructionBool_eq {tau nu : ℤ} (z : QuadInt tau nu) (k : ℕ) :
    pairLightFloorObstructionBool tau nu (pairLightCoordinates z) k =
      QuadInt.floorObstructionBool z k := by
  dsimp only [pairLightFloorObstructionBool, pairLightNorm, pairLightCoordinates]
  simp only [QuadInt.floorObstructionBool, QuadInt.norm_formula, Int.ofNat_eq_natCast] <;> rfl

/-- Every tail position, invalid tag, duplicate, guard branch and floor-list
case has exactly the old result. There is no data-validity premise. -/
theorem _root_.solution {tau nu : ℤ}
    (sieve : List (ℕ × ℕ)) (x : PairResidueVertex tau nu)
    (ys : List (PairResidueVertex tau nu)) (code : ℕ) (ks : List ℕ) :
    pairLightSelectedFloorRowBool tau nu sieve (pairLightCachedCoordinates x)
      (ys.map pairLightCachedCoordinates) code ks =
      pairRawSelectedFloorRowBool sieve x ys code ks := by
  induction ys generalizing code ks with
  | nil => rfl
  | cons y ys ih =>
      simp only [pairLightCachedCoordinates] at ih
      cases ks <;>
        simp only [List.map_cons, pairLightSelectedFloorRowBool,
          pairRawSelectedFloorRowBool, pairLightCachedCoordinates,
          pairLightSelectedMaskRejectBool_eq_raw, pairLightCoordinates_eq_iff,
          pairLightProductPlusOne_eq, pairLightNegativeIntegerObstructionBool_eq,
          pairLightFloorObstructionBool_eq, ih]











end D1Bound5
end
