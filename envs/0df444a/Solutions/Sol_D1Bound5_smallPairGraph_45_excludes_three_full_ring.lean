-- Prove2me | solution 1 for D1Bound5.smallPairGraph_45_excludes_three_full_ring
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:33:34.281586+00:00
-- url     : https://prove2.me/submissions/a7093f1e-deb8-441c-bfc1-6933ff240935

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
import Definitions.Def_D1Bound5_SmallPairGraphCheck_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphData45_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphData45_Definitions_002
import Definitions.Def_D1Bound5_SmallPairSieve_1_5_Definitions
import Definitions.Def_D1Bound5_SquareTest_Definitions
import Definitions.Def_D1Bound5_TwoSmallSeedDisks_Definitions
import Theorems.Thm_D1Bound5_PairLightPrepared45_left_checked
import Theorems.Thm_D1Bound5_PairLightPrepared45_right_checked
import Theorems.Thm_D1Bound5_QuadInt_hasSquareRoot_iff
import Theorems.Thm_D1Bound5_pairGraphTriangleFreeBool_of_split
import Theorems.Thm_D1Bound5_seedRootDisk_1_5_eq
import Theorems.Thm_D1Bound5_smallPairClosure_45_checked
import Theorems.Thm_D1Bound5_smallPairFilter_45_checked
import Theorems.Thm_D1Bound5_smallPairSeeds_45_checked
import Theorems.Thm_D1Bound5_smallPairSieve_1_5_valid
import Theorems.Thm_D1Bound5_small_pair_graph_excludes_three_full_ring

section
/- Preserved body from D1Bound5.SmallPairGraphInputs45; original SHA256 e005e2e8cd75649429508b44f8449f6119b1af70789808e26eb05b3deea835d1. -/

namespace D1Bound5
set_option maxRecDepth 100000

open QuadInt








namespace PairGraphPrepared45



end PairGraphPrepared45
end D1Bound5

/- Preserved body from D1Bound5.SmallPairGraphArithmetic45; original SHA256 3a94fa935fa21ad5943c323eba44b6f35df957553b7d8649176809e361d51776. -/

namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0







end D1Bound5

/- Preserved body from D1Bound5.SmallPairGraphWitnessData45; original SHA256 5f07a239e6e5d926162b0a89c88c4e5e19bf9ed2c077da34499a3eaf01573086. -/

namespace D1Bound5.PairGraphPrepared45
set_option maxRecDepth 100000









end D1Bound5.PairGraphPrepared45

/- Preserved body from D1Bound5.SmallPairGraphClosure45; original SHA256 a8e126e0ea71de1ea4fb613714cd6df1bb0f1f365d315068cb7ca1965805c4b5. -/

namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared45





end D1Bound5

/- Preserved body from D1Bound5.SmallPairRawSelectedData45; original SHA256 65ac4f5dfac9d6e9fbbc457210c34487e3fe2bc52c553f1bf2e8620e0971f157. -/

namespace D1Bound5.PairSelectedPrepared45
set_option maxRecDepth 100000









end D1Bound5.PairSelectedPrepared45

/- Preserved body from D1Bound5.SmallPairLightAssembly45; original SHA256 ca0792cbca80dc647182dd3f457cd828d94bd590ac4a226175f3d673683d7b8c. -/

namespace D1Bound5.PairLightPrepared45
set_option maxRecDepth 100000
set_option maxHeartbeats 0



















end D1Bound5.PairLightPrepared45

/- Preserved body from D1Bound5.SmallPairGraphTriangle45; original SHA256 350e1602c0b0fbb99542419ef70a981c0070ba309dfe2268bd9f355a70eb5aaa. -/

namespace D1Bound5
set_option maxRecDepth 100000

theorem smallPairNoTriangle_45_checked :
    pairGraphTriangleFreeBool smallPairSieve_1_5 smallPairLarge_45 = true :=
  pairGraphTriangleFreeBool_of_split smallPairSieve_1_5 smallPairLarge_45 PairGraphPrepared45.colors
    PairLightPrepared45.left_checked PairLightPrepared45.right_checked

end D1Bound5

/- Preserved body from D1Bound5.SmallPairGraphData45; original SHA256 0932d1428f25bf1fbddb795e60ed173381edd6d1ae54456d0fbf29b9282010db. -/
end

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt

/-- Complete large-extension triangle exclusion for pair-table row 45. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (e : QuadInt 1 5 ≃+* 𝓞 K) (t : Fin 3 → QuadInt 1 5)
    (ht : IsD1Tuple t)
    (hpair : ∀ i, PairExtension smallPairA_45 smallPairB_45 (t i))
    (hlarge : ∀ i, 9 ≤ (t i).norm) (hbound : ∀ i, (t i).norm ≤ 10^1100)
    (hneA : ∀ i, t i ≠ smallPairA_45) (hneB : ∀ i, t i ≠ smallPairB_45) : False := by
  have hpos : 0 < discriminant 1 5 := by decide
  have hroot : ∃ r0, r0*r0 = smallPairA_45*smallPairB_45+1 :=
    (hasSquareRoot_iff hpos _).1 (by decide +kernel)
  apply small_pair_graph_excludes_three_full_ring hK phi hpos e smallPairA_45 smallPairB_45
    (by decide) (by decide) (by decide) hroot (by decide) (by decide)
    (10^1100) seedRootDisk_1_5 smallPairClosure_45 smallPairLarge_45
    smallPairSieve_1_5 smallPairSieve_1_5_valid ?_
    smallPairSeeds_45_checked smallPairClosure_45_checked smallPairFilter_45_checked
    smallPairNoTriangle_45_checked t ht hpair hlarge hbound hneA hneB
  intro q hq
  rw [seedRootDisk_1_5_eq, List.mem_toFinset] at hq
  exact hq

end D1Bound5
end
