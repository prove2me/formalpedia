-- Prove2me | solution 1 for D1Bound5.smallPairGraph_38_excludes_three_full_ring
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:33:17.036164+00:00
-- url     : https://prove2.me/submissions/68e35a34-7bb2-46c5-b65d-84cadf557cd4

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
import Definitions.Def_D1Bound5_SmallPairGraphData38_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphData38_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphData38_Definitions_003
import Definitions.Def_D1Bound5_SmallPairGraphData38_Definitions_004
import Definitions.Def_D1Bound5_SmallPairSieve_1_2_Definitions
import Definitions.Def_D1Bound5_SquareTest_Definitions
import Theorems.Thm_D1Bound5_PairLightPrepared38_left_checked
import Theorems.Thm_D1Bound5_PairLightPrepared38_right_checked
import Theorems.Thm_D1Bound5_QuadInt_hasSquareRoot_iff
import Theorems.Thm_D1Bound5_pairGraphTriangleFreeBool_of_split
import Theorems.Thm_D1Bound5_seedRootDisk_1_2_eq
import Theorems.Thm_D1Bound5_smallPairClosure_38_checked
import Theorems.Thm_D1Bound5_smallPairFilter_38_checked
import Theorems.Thm_D1Bound5_smallPairSeeds_38_checked
import Theorems.Thm_D1Bound5_smallPairSieve_1_2_valid
import Theorems.Thm_D1Bound5_small_pair_graph_excludes_three_full_ring

section
/- Preserved body from D1Bound5.SmallPairGraphInputs38; original SHA256 e84905f2c584eaec762f49ff95cacb67eda33b4f26e2c70c9b7b8b2cce33bac3. -/

namespace D1Bound5
set_option maxRecDepth 100000

open QuadInt








namespace PairGraphPrepared38



end PairGraphPrepared38
end D1Bound5

/- Preserved body from D1Bound5.SmallPairGraphArithmetic38; original SHA256 dd8dbfa6abf4d50ab024f61aee47d820a823b926c36e406836f87c60656daee7. -/

namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0







end D1Bound5

/- Preserved body from D1Bound5.SmallPairGraphWitnessData38; original SHA256 c6164df96db4aa1be0a86091c70be1a406e41f83d72c88d46eabb3e7189c3052. -/

namespace D1Bound5.PairGraphPrepared38
set_option maxRecDepth 100000









end D1Bound5.PairGraphPrepared38

/- Preserved body from D1Bound5.SmallPairGraphClosure38; original SHA256 b10bc5b53ff5864b17af0b52e70793fe0d0cc33ca5726ae8e59895847f319d29. -/

namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared38





end D1Bound5

/- Preserved body from D1Bound5.SmallPairRawSelectedData38; original SHA256 bc91510fcbc172095a6e7f20939407122422a55cd73446afa31e0b04776daec7. -/

namespace D1Bound5.PairSelectedPrepared38
set_option maxRecDepth 100000









end D1Bound5.PairSelectedPrepared38

/- Preserved body from D1Bound5.SmallPairLightAssembly38; original SHA256 0a6d4a5a2f8cf5b522f0c22f64572b8fe8962d975aa36145b357f51474e4371c. -/

namespace D1Bound5.PairLightPrepared38
set_option maxRecDepth 100000
set_option maxHeartbeats 0



















end D1Bound5.PairLightPrepared38

/- Preserved body from D1Bound5.SmallPairGraphTriangle38; original SHA256 cb5933e1c0e765de3430434a98639be128637fe79d2d295f12b7f83e963f8872. -/

namespace D1Bound5
set_option maxRecDepth 100000

theorem smallPairNoTriangle_38_checked :
    pairGraphTriangleFreeBool smallPairSieve_1_2 smallPairLarge_38 = true :=
  pairGraphTriangleFreeBool_of_split smallPairSieve_1_2 smallPairLarge_38 PairGraphPrepared38.colors
    PairLightPrepared38.left_checked PairLightPrepared38.right_checked

end D1Bound5

/- Preserved body from D1Bound5.SmallPairGraphData38; original SHA256 83f2c3bd68777968da247a58362b3e2051ce156b248c76a29c29eb55c1278ea0. -/
end

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt

/-- Complete large-extension triangle exclusion for pair-table row 38. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (e : QuadInt 1 2 ≃+* 𝓞 K) (t : Fin 3 → QuadInt 1 2)
    (ht : IsD1Tuple t)
    (hpair : ∀ i, PairExtension smallPairA_38 smallPairB_38 (t i))
    (hlarge : ∀ i, 9 ≤ (t i).norm) (hbound : ∀ i, (t i).norm ≤ 10^1100)
    (hneA : ∀ i, t i ≠ smallPairA_38) (hneB : ∀ i, t i ≠ smallPairB_38) : False := by
  have hpos : 0 < discriminant 1 2 := by decide
  have hroot : ∃ r0, r0*r0 = smallPairA_38*smallPairB_38+1 :=
    (hasSquareRoot_iff hpos _).1 (by decide +kernel)
  apply small_pair_graph_excludes_three_full_ring hK phi hpos e smallPairA_38 smallPairB_38
    (by decide) (by decide) (by decide) hroot (by decide) (by decide)
    (10^1100) seedRootDisk_1_2 smallPairClosure_38 smallPairLarge_38
    smallPairSieve_1_2 smallPairSieve_1_2_valid ?_
    smallPairSeeds_38_checked smallPairClosure_38_checked smallPairFilter_38_checked
    smallPairNoTriangle_38_checked t ht hpair hlarge hbound hneA hneB
  intro q hq
  rw [seedRootDisk_1_2_eq, List.mem_toFinset] at hq
  exact hq

end D1Bound5
end
