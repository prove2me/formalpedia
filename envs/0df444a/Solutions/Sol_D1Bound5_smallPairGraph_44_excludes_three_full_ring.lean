-- Prove2me | solution 1 for D1Bound5.smallPairGraph_44_excludes_three_full_ring
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:33:53.605022+00:00
-- url     : https://prove2.me/submissions/29761170-0019-413d-aee5-c6ea632f150f

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
import Definitions.Def_D1Bound5_SmallPairGraphData44_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphData44_Definitions_002
import Definitions.Def_D1Bound5_SmallPairSieve_1_4_Definitions
import Definitions.Def_D1Bound5_SquareTest_Definitions
import Definitions.Def_D1Bound5_TwoSmallSeedDisks_Definitions
import Theorems.Thm_D1Bound5_PairLightPrepared44_left_checked
import Theorems.Thm_D1Bound5_PairLightPrepared44_right_checked
import Theorems.Thm_D1Bound5_QuadInt_hasSquareRoot_iff
import Theorems.Thm_D1Bound5_pairGraphTriangleFreeBool_of_split
import Theorems.Thm_D1Bound5_seedRootDisk_1_4_eq
import Theorems.Thm_D1Bound5_smallPairClosure_44_checked
import Theorems.Thm_D1Bound5_smallPairFilter_44_checked
import Theorems.Thm_D1Bound5_smallPairSeeds_44_checked
import Theorems.Thm_D1Bound5_smallPairSieve_1_4_valid
import Theorems.Thm_D1Bound5_small_pair_graph_excludes_three_full_ring

section
/- Preserved body from D1Bound5.SmallPairGraphInputs44; original SHA256 b443d2cf11af364c9d9082712786db2cf3a153851a5eaea7bdbb30c84d99fec0. -/

namespace D1Bound5
set_option maxRecDepth 100000

open QuadInt








namespace PairGraphPrepared44



end PairGraphPrepared44
end D1Bound5

/- Preserved body from D1Bound5.SmallPairGraphArithmetic44; original SHA256 f6bdb5a40012c0b78d1ce6330b64244084b8e6a6e3c41c9a3690017b0eb6f558. -/

namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0







end D1Bound5

/- Preserved body from D1Bound5.SmallPairGraphWitnessData44; original SHA256 f3c4a787d1e9f9d4f74a295674b17167e04ca7bbd68b05e1aafe83388608421d. -/

namespace D1Bound5.PairGraphPrepared44
set_option maxRecDepth 100000









end D1Bound5.PairGraphPrepared44

/- Preserved body from D1Bound5.SmallPairGraphClosure44; original SHA256 4dfcf91b3104c4a07c5f9491b4956fa7d08ee63ada7f4c55131fc45e109a31eb. -/

namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared44





end D1Bound5

/- Preserved body from D1Bound5.SmallPairRawSelectedData44; original SHA256 6f4738d9d44c74a5377009120c16bff87092df004b921c6c5d7740d606704914. -/

namespace D1Bound5.PairSelectedPrepared44
set_option maxRecDepth 100000









end D1Bound5.PairSelectedPrepared44

/- Preserved body from D1Bound5.SmallPairLightAssembly44; original SHA256 72a386daf4c4fbc03e4bc740cfffed37a9495da0a7c0832f363d927056f2fbd1. -/

namespace D1Bound5.PairLightPrepared44
set_option maxRecDepth 100000
set_option maxHeartbeats 0



















end D1Bound5.PairLightPrepared44

/- Preserved body from D1Bound5.SmallPairGraphTriangle44; original SHA256 b0b577b7778dee384454132602d0d9a1898801dd28bbf0a19bb7e4a67095b933. -/

namespace D1Bound5
set_option maxRecDepth 100000

theorem smallPairNoTriangle_44_checked :
    pairGraphTriangleFreeBool smallPairSieve_1_4 smallPairLarge_44 = true :=
  pairGraphTriangleFreeBool_of_split smallPairSieve_1_4 smallPairLarge_44 PairGraphPrepared44.colors
    PairLightPrepared44.left_checked PairLightPrepared44.right_checked

end D1Bound5

/- Preserved body from D1Bound5.SmallPairGraphData44; original SHA256 71cc4347dc31ae756ab45cd633715fbc8dd66b09ec47b721c35b4874848ddc7a. -/
end

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt

/-- Complete large-extension triangle exclusion for pair-table row 44. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (e : QuadInt 1 4 ≃+* 𝓞 K) (t : Fin 3 → QuadInt 1 4)
    (ht : IsD1Tuple t)
    (hpair : ∀ i, PairExtension smallPairA_44 smallPairB_44 (t i))
    (hlarge : ∀ i, 9 ≤ (t i).norm) (hbound : ∀ i, (t i).norm ≤ 10^1100)
    (hneA : ∀ i, t i ≠ smallPairA_44) (hneB : ∀ i, t i ≠ smallPairB_44) : False := by
  have hpos : 0 < discriminant 1 4 := by decide
  have hroot : ∃ r0, r0*r0 = smallPairA_44*smallPairB_44+1 :=
    (hasSquareRoot_iff hpos _).1 (by decide +kernel)
  apply small_pair_graph_excludes_three_full_ring hK phi hpos e smallPairA_44 smallPairB_44
    (by decide) (by decide) (by decide) hroot (by decide) (by decide)
    (10^1100) seedRootDisk_1_4 smallPairClosure_44 smallPairLarge_44
    smallPairSieve_1_4 smallPairSieve_1_4_valid ?_
    smallPairSeeds_44_checked smallPairClosure_44_checked smallPairFilter_44_checked
    smallPairNoTriangle_44_checked t ht hpair hlarge hbound hneA hneB
  intro q hq
  rw [seedRootDisk_1_4_eq, List.mem_toFinset] at hq
  exact hq

end D1Bound5
end
