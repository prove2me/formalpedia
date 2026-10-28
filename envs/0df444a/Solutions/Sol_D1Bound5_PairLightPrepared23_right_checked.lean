-- Prove2me | solution 1 for D1Bound5.PairLightPrepared23.right_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:39:43.080188+00:00
-- url     : https://prove2.me/submissions/f0a73b9e-3bf9-4070-80be-109c53185034

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs23_Definitions_003
import Definitions.Def_D1Bound5_SmallPairGraphInputs23_Definitions_004
import Definitions.Def_D1Bound5_SmallPairLightData23RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23RightVertices_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23Sieve_Definitions
import Definitions.Def_D1Bound5_SmallPairRawSelectedData23RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairRawSelectedData23RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairSieve_1_1_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_right_coverage_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_right_signatures_checked
import Theorems.Thm_D1Bound5_PairLightPrepared23_rightVertices_eq
import Theorems.Thm_D1Bound5_PairLightPrepared23_right_coverage_checked
import Theorems.Thm_D1Bound5_PairLightPrepared23_right_independent_checked
import Theorems.Thm_D1Bound5_PairLightPrepared23_right_signatures_checked
import Theorems.Thm_D1Bound5_PairLightPrepared23_sieve_eq
import Theorems.Thm_D1Bound5_pairIndependentBool_of_light_selected_floor_certificate

section
namespace D1Bound5.PairLightPrepared23
set_option maxRecDepth 100000
set_option maxHeartbeats 0







theorem right_certificate_checked :
    pairLightSelectedFloorIndependentCertificateBool 1 1 sieve
      rightVertices rightCached rightRows = true := by
  unfold pairLightSelectedFloorIndependentCertificateBool
  exact Bool.and_eq_true_iff.mpr ⟨right_coverage_checked,
    Bool.and_eq_true_iff.mpr ⟨right_signatures_checked, right_independent_checked⟩⟩

end D1Bound5.PairLightPrepared23
end

section
namespace D1Bound5.PairLightPrepared23
set_option maxRecDepth 100000
set_option maxHeartbeats 0













theorem rightCached_eq :
    rightCached = PairSelectedPrepared23.rightCached.map pairLightCachedCoordinates := by
  rfl

theorem rightRows_eq : rightRows = PairSelectedPrepared23.rightRows := by
  rfl

theorem _root_.solution :
    pairIndependentBool smallPairSieve_1_1 (pairSplitByMask smallPairLarge_23 PairGraphPrepared23.colors).2 = true := by
  apply pairIndependentBool_of_light_selected_floor_certificate (by decide) smallPairSieve_1_1
    (pairSplitByMask smallPairLarge_23 PairGraphPrepared23.colors).2 PairSelectedPrepared23.rightCached PairSelectedPrepared23.rightRows
  rw [← sieve_eq, ← rightVertices_eq, ← rightCached_eq, ← rightRows_eq]
  exact right_certificate_checked

end D1Bound5.PairLightPrepared23
end
