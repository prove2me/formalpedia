-- Prove2me | solution 1 for D1Bound5.PairLightPilot34.left_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:27:59.821351+00:00
-- url     : https://prove2.me/submissions/f46dd158-9276-4f79-9ff9-60399e436bac

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
import Mathlib.Data.List.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_PairBipartiteCheck_Definitions
import Definitions.Def_D1Bound5_PairCachedResidues_Definitions
import Definitions.Def_D1Bound5_PairLightArithmeticBridge_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphInputs34_Definitions_003
import Definitions.Def_D1Bound5_SmallPairGraphInputs34_Definitions_004
import Definitions.Def_D1Bound5_SmallPairLightData34_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData34_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLiteralCachedData34_Definitions_001
import Definitions.Def_D1Bound5_SmallPairSelectedData34_Definitions
import Definitions.Def_D1Bound5_SmallPairSieve_1_2_Definitions
import Theorems.Thm_D1Bound5_PairLightPilot34_leftVertices_eq
import Theorems.Thm_D1Bound5_PairLightPilot34_left_certificate_checked
import Theorems.Thm_D1Bound5_pairIndependentBool_of_light_selected_floor_certificate

section
namespace D1Bound5.PairLightPilot34
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- All masks and their order are the original sieve. -/
theorem sieve_eq : sieve = smallPairSieve_1_2 := by
  rfl



/-- Every original cached coordinate and supplied signature is retained. -/
theorem leftCached_eq :
    leftCached = PairLiteralPilot34.leftCached.map pairLightCachedCoordinates := by
  rfl

/-- Packed words and sparse floor witnesses are unchanged. -/
theorem leftRows_eq : leftRows = PairSelectedPilot34.leftRows := by
  rfl

/-- Exactly the original left independent-class assertion, obtained only after
the four concrete data equalities and the unconditional checker bridge. -/
theorem _root_.solution :
    pairIndependentBool smallPairSieve_1_2
      (pairSplitByMask smallPairLarge_34 PairGraphPrepared34.colors).1 = true := by
  apply pairIndependentBool_of_light_selected_floor_certificate (by decide) smallPairSieve_1_2
    (pairSplitByMask smallPairLarge_34 PairGraphPrepared34.colors).1
    PairLiteralPilot34.leftCached PairSelectedPilot34.leftRows
  rw [← sieve_eq, ← leftVertices_eq, ← leftCached_eq, ← leftRows_eq]
  exact left_certificate_checked

end D1Bound5.PairLightPilot34
end
