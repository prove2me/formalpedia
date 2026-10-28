-- Prove2me | solution 1 for D1Bound5.PairLightPrepared19.left_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:19:21.23548+00:00
-- url     : https://prove2.me/submissions/0ff19bf1-bd8f-4e6a-9253-d087d866dbfe

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs19_Definitions_003
import Definitions.Def_D1Bound5_SmallPairGraphInputs19_Definitions_004
import Definitions.Def_D1Bound5_SmallPairLightData19LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19LeftVertices_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19Sieve_Definitions
import Definitions.Def_D1Bound5_SmallPairRawSelectedData19LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairRawSelectedData19LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairSieve_1_1_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared19_left_coverage_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared19_left_signatures_checked
import Theorems.Thm_D1Bound5_PairLightPrepared19_leftVertices_eq
import Theorems.Thm_D1Bound5_PairLightPrepared19_left_coverage_checked
import Theorems.Thm_D1Bound5_PairLightPrepared19_left_independent_checked
import Theorems.Thm_D1Bound5_PairLightPrepared19_left_signatures_checked
import Theorems.Thm_D1Bound5_PairLightPrepared19_sieve_eq
import Theorems.Thm_D1Bound5_pairIndependentBool_of_light_selected_floor_certificate

section
namespace D1Bound5.PairLightPrepared19
set_option maxRecDepth 100000
set_option maxHeartbeats 0







theorem left_certificate_checked :
    pairLightSelectedFloorIndependentCertificateBool 1 1 sieve
      leftVertices leftCached leftRows = true := by
  unfold pairLightSelectedFloorIndependentCertificateBool
  exact Bool.and_eq_true_iff.mpr ⟨left_coverage_checked,
    Bool.and_eq_true_iff.mpr ⟨left_signatures_checked, left_independent_checked⟩⟩

end D1Bound5.PairLightPrepared19
end

section
namespace D1Bound5.PairLightPrepared19
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem leftCached_eq :
    leftCached = PairSelectedPrepared19.leftCached.map pairLightCachedCoordinates := by
  rfl

theorem leftRows_eq : leftRows = PairSelectedPrepared19.leftRows := by
  rfl

theorem _root_.solution :
    pairIndependentBool smallPairSieve_1_1 (pairSplitByMask smallPairLarge_19 PairGraphPrepared19.colors).1 = true := by
  apply pairIndependentBool_of_light_selected_floor_certificate (by decide) smallPairSieve_1_1
    (pairSplitByMask smallPairLarge_19 PairGraphPrepared19.colors).1 PairSelectedPrepared19.leftCached PairSelectedPrepared19.leftRows
  rw [← sieve_eq, ← leftVertices_eq, ← leftCached_eq, ← leftRows_eq]
  exact left_certificate_checked









end D1Bound5.PairLightPrepared19
end
