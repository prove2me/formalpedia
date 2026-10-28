-- Prove2me | solution 1 for D1Bound5.smallPairGraph_20_excludes_three_full_ring
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:33:25.525389+00:00
-- url     : https://prove2.me/submissions/537926fe-8a4b-40d6-ac42-8835595752b8

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
import Definitions.Def_D1Bound5_DiskEnumeration_Definitions
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_PairExtensionCore_Definitions
import Definitions.Def_D1Bound5_PairSeedDisks_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphCheck_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphData20_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphData20_Definitions_002
import Definitions.Def_D1Bound5_SmallPairSieve_1_1_Definitions
import Definitions.Def_D1Bound5_SquareTest_Definitions
import Theorems.Thm_D1Bound5_PairLightPrepared20_left_checked
import Theorems.Thm_D1Bound5_PairLightPrepared20_right_checked
import Theorems.Thm_D1Bound5_QuadInt_hasSquareRoot_iff
import Theorems.Thm_D1Bound5_pairGraphTriangleFreeBool_of_split
import Theorems.Thm_D1Bound5_seedRootDisk_1_1_eq
import Theorems.Thm_D1Bound5_smallPairClosure_20_checked
import Theorems.Thm_D1Bound5_smallPairFilter_20_checked
import Theorems.Thm_D1Bound5_smallPairSeeds_20_checked
import Theorems.Thm_D1Bound5_smallPairSieve_1_1_valid
import Theorems.Thm_D1Bound5_small_pair_graph_excludes_three_full_ring

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



















end D1Bound5.PairLightPrepared20

/- Preserved body from D1Bound5.SmallPairGraphTriangle20; original SHA256 0f462aad8893a82f742f0b56d9594b16a957932c01a4eaba7dd9fdc634acd11f. -/

namespace D1Bound5
set_option maxRecDepth 100000

theorem smallPairNoTriangle_20_checked :
    pairGraphTriangleFreeBool smallPairSieve_1_1 smallPairLarge_20 = true :=
  pairGraphTriangleFreeBool_of_split smallPairSieve_1_1 smallPairLarge_20 PairGraphPrepared20.colors
    PairLightPrepared20.left_checked PairLightPrepared20.right_checked

end D1Bound5

/- Preserved body from D1Bound5.SmallPairGraphData20; original SHA256 1119064079b00d9ec80f1ebe6b141ad835f0a002382948c7b7b9b623a9e424ce. -/
end

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt

/-- Complete large-extension triangle exclusion for pair-table row 20. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (e : QuadInt 1 1 ≃+* 𝓞 K) (t : Fin 3 → QuadInt 1 1)
    (ht : IsD1Tuple t)
    (hpair : ∀ i, PairExtension smallPairA_20 smallPairB_20 (t i))
    (hlarge : ∀ i, 9 ≤ (t i).norm) (hbound : ∀ i, (t i).norm ≤ 10^1100)
    (hneA : ∀ i, t i ≠ smallPairA_20) (hneB : ∀ i, t i ≠ smallPairB_20) : False := by
  have hpos : 0 < discriminant 1 1 := by decide
  have hroot : ∃ r0, r0*r0 = smallPairA_20*smallPairB_20+1 :=
    (hasSquareRoot_iff hpos _).1 (by decide +kernel)
  apply small_pair_graph_excludes_three_full_ring hK phi hpos e smallPairA_20 smallPairB_20
    (by decide) (by decide) (by decide) hroot (by decide) (by decide)
    (10^1100) seedRootDisk_1_1 smallPairClosure_20 smallPairLarge_20
    smallPairSieve_1_1 smallPairSieve_1_1_valid ?_
    smallPairSeeds_20_checked smallPairClosure_20_checked smallPairFilter_20_checked
    smallPairNoTriangle_20_checked t ht hpair hlarge hbound hneA hneB
  intro q hq
  rw [seedRootDisk_1_1_eq, List.mem_toFinset] at hq
  exact hq

end D1Bound5
end
