-- Prove2me | solution 1 for D1Bound5.PairLightPrepared20.left_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:30:37.34909+00:00
-- url     : https://prove2.me/submissions/e47757a5-2515-4b70-9e7d-a664cc9d4335

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
import Mathlib.Data.List.Range
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
import Definitions.Def_D1Bound5_SmallPairGraphData20_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphData20_Definitions_004
import Definitions.Def_D1Bound5_SmallPairLightData20_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData20_Definitions_002
import Definitions.Def_D1Bound5_SmallPairSieve_1_1_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared20_left_coverage_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared20_left_signatures_checked
import Theorems.Thm_D1Bound5_PairLightPrepared20_leftVertices_eq
import Theorems.Thm_D1Bound5_PairLightPrepared20_left_coverage_checked
import Theorems.Thm_D1Bound5_PairLightPrepared20_left_independent_checked
import Theorems.Thm_D1Bound5_PairLightPrepared20_left_signatures_checked
import Theorems.Thm_D1Bound5_PairLightPrepared20_sieve_eq
import Theorems.Thm_D1Bound5_pairIndependentBool_of_light_selected_floor_certificate

section
namespace D1Bound5.PairLightPrepared20
set_option maxRecDepth 100000
set_option maxHeartbeats 0







theorem left_certificate_checked :
    pairLightSelectedFloorIndependentCertificateBool 1 1 sieve
      leftVertices leftCached leftRows = true := by
  unfold pairLightSelectedFloorIndependentCertificateBool
  exact Bool.and_eq_true_iff.mpr ⟨left_coverage_checked,
    Bool.and_eq_true_iff.mpr ⟨left_signatures_checked, left_independent_checked⟩⟩

end D1Bound5.PairLightPrepared20
end

section
/- Preserved body from D1Bound5.SmallPairGraphInputs20; original SHA256 bc9ab6842f90c07abbe4d0b2e4e275015a536372ae9d8e3b88ffc4202e0d5aed. -/

namespace D1Bound5
set_option maxRecDepth 100000

open QuadInt








namespace PairGraphPrepared20



end PairGraphPrepared20
end D1Bound5

/- Preserved body from D1Bound5.SmallPairGraphArithmetic20; original SHA256 0b6a860926a534df996ddb1796bb9beb2a5c1af462303e1cd6f0bef39ef96aab. -/

namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0







end D1Bound5

/- Preserved body from D1Bound5.SmallPairGraphWitnessData20; original SHA256 bf4a3f7c5bd1636f4f0ad83205e7f4af58a1a3d122aee19363f51b529f2e6e1c. -/

namespace D1Bound5.PairGraphPrepared20
set_option maxRecDepth 100000









end D1Bound5.PairGraphPrepared20

/- Preserved body from D1Bound5.SmallPairGraphClosure20; original SHA256 c15afd21ec15dc8ae435b2b616701248219316938385cffce13b511f22894b58. -/

namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared20





end D1Bound5

/- Preserved body from D1Bound5.SmallPairRawSelectedData20; original SHA256 1eced1959592632a55609d89f05afdd195a90e8c1529f17f069edd652883df21. -/

namespace D1Bound5.PairSelectedPrepared20
set_option maxRecDepth 100000









end D1Bound5.PairSelectedPrepared20

/- Preserved body from D1Bound5.SmallPairLightAssembly20; original SHA256 35ac07c73ba1ebb8e00e84d4c2d38cb8c1da79cd790183510d1443374fd7af35. -/

namespace D1Bound5.PairLightPrepared20
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem leftCached_eq :
    leftCached = PairSelectedPrepared20.leftCached.map pairLightCachedCoordinates := by
  rfl

theorem leftRows_eq : leftRows = PairSelectedPrepared20.leftRows := by
  rfl

theorem _root_.solution :
    pairIndependentBool smallPairSieve_1_1 (pairSplitByMask smallPairLarge_20 PairGraphPrepared20.colors).1 = true := by
  apply pairIndependentBool_of_light_selected_floor_certificate (by decide) smallPairSieve_1_1
    (pairSplitByMask smallPairLarge_20 PairGraphPrepared20.colors).1 PairSelectedPrepared20.leftCached PairSelectedPrepared20.leftRows
  rw [← sieve_eq, ← leftVertices_eq, ← leftCached_eq, ← leftRows_eq]
  exact left_certificate_checked









end D1Bound5.PairLightPrepared20

/- Preserved body from D1Bound5.SmallPairGraphTriangle20; original SHA256 0f462aad8893a82f742f0b56d9594b16a957932c01a4eaba7dd9fdc634acd11f. -/

namespace D1Bound5
set_option maxRecDepth 100000



end D1Bound5

/- Preserved body from D1Bound5.SmallPairGraphData20; original SHA256 1119064079b00d9ec80f1ebe6b141ad835f0a002382948c7b7b9b623a9e424ce. -/
end
