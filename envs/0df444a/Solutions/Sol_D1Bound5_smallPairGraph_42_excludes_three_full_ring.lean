-- Prove2me | solution 1 for D1Bound5.smallPairGraph_42_excludes_three_full_ring
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:33:52.162524+00:00
-- url     : https://prove2.me/submissions/8e337114-f8e4-4015-94f0-a4a3a2cf9475

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
import Definitions.Def_D1Bound5_SmallPairGraphData42_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphData42_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphData42_Definitions_003
import Definitions.Def_D1Bound5_SmallPairGraphData42_Definitions_004
import Definitions.Def_D1Bound5_SmallPairSieve_1_3_Definitions
import Definitions.Def_D1Bound5_SquareTest_Definitions
import Definitions.Def_D1Bound5_TwoSmallSeedDisks_Definitions
import Theorems.Thm_D1Bound5_PairLightPrepared42_left_checked
import Theorems.Thm_D1Bound5_PairLightPrepared42_right_checked
import Theorems.Thm_D1Bound5_QuadInt_hasSquareRoot_iff
import Theorems.Thm_D1Bound5_pairGraphTriangleFreeBool_of_split
import Theorems.Thm_D1Bound5_seedRootDisk_1_3_eq
import Theorems.Thm_D1Bound5_smallPairClosure_42_checked
import Theorems.Thm_D1Bound5_smallPairFilter_42_checked
import Theorems.Thm_D1Bound5_smallPairSeeds_42_checked
import Theorems.Thm_D1Bound5_smallPairSieve_1_3_valid
import Theorems.Thm_D1Bound5_small_pair_graph_excludes_three_full_ring

section
/- Preserved body from D1Bound5.SmallPairGraphInputs42; original SHA256 e751a5007e71d6837bdcdd3b8c93aacd9a20b359f3364e1165d9ae650d464a20. -/

namespace D1Bound5
set_option maxRecDepth 100000

open QuadInt








namespace PairGraphPrepared42



end PairGraphPrepared42
end D1Bound5

/- Preserved body from D1Bound5.SmallPairGraphArithmetic42; original SHA256 11d316a549a5c95b93a9ed98fc580dafac8bfeae3a40c435639662a2c047d64e. -/

namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0







end D1Bound5

/- Preserved body from D1Bound5.SmallPairGraphWitnessData42; original SHA256 709c0bd6914ee1c1181f151840da49be63f2fae2e4de4d163170b17c5dc72c11. -/

namespace D1Bound5.PairGraphPrepared42
set_option maxRecDepth 100000









end D1Bound5.PairGraphPrepared42

/- Preserved body from D1Bound5.SmallPairGraphClosure42; original SHA256 2f7911b205f189a4b5a1cc26fedf3608921021ba95e39dc0344768ee9a21263e. -/

namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared42





end D1Bound5

/- Preserved body from D1Bound5.SmallPairRawSelectedData42; original SHA256 245fb4473f619e3d17a60299f8662a982d483bd8ab8f2abc1366b272dd797def. -/

namespace D1Bound5.PairSelectedPrepared42
set_option maxRecDepth 100000









end D1Bound5.PairSelectedPrepared42

/- Preserved body from D1Bound5.SmallPairLightAssembly42; original SHA256 60c90a5f9d67d181917899dbdbbad52af21334e0b65779e96864677d03075657. -/

namespace D1Bound5.PairLightPrepared42
set_option maxRecDepth 100000
set_option maxHeartbeats 0



















end D1Bound5.PairLightPrepared42

/- Preserved body from D1Bound5.SmallPairGraphTriangle42; original SHA256 91c579c9ca406a72e9bd3b12d424418d47a488728036d60bd1046b2dca9865fe. -/

namespace D1Bound5
set_option maxRecDepth 100000

theorem smallPairNoTriangle_42_checked :
    pairGraphTriangleFreeBool smallPairSieve_1_3 smallPairLarge_42 = true :=
  pairGraphTriangleFreeBool_of_split smallPairSieve_1_3 smallPairLarge_42 PairGraphPrepared42.colors
    PairLightPrepared42.left_checked PairLightPrepared42.right_checked

end D1Bound5

/- Preserved body from D1Bound5.SmallPairGraphData42; original SHA256 fe2f13df896894ce55ebbe0d8a39f9ac40b2578d241debfd77f1b8603357b039. -/
end

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt

/-- Complete large-extension triangle exclusion for pair-table row 42. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (e : QuadInt 1 3 ≃+* 𝓞 K) (t : Fin 3 → QuadInt 1 3)
    (ht : IsD1Tuple t)
    (hpair : ∀ i, PairExtension smallPairA_42 smallPairB_42 (t i))
    (hlarge : ∀ i, 9 ≤ (t i).norm) (hbound : ∀ i, (t i).norm ≤ 10^1100)
    (hneA : ∀ i, t i ≠ smallPairA_42) (hneB : ∀ i, t i ≠ smallPairB_42) : False := by
  have hpos : 0 < discriminant 1 3 := by decide
  have hroot : ∃ r0, r0*r0 = smallPairA_42*smallPairB_42+1 :=
    (hasSquareRoot_iff hpos _).1 (by decide +kernel)
  apply small_pair_graph_excludes_three_full_ring hK phi hpos e smallPairA_42 smallPairB_42
    (by decide) (by decide) (by decide) hroot (by decide) (by decide)
    (10^1100) seedRootDisk_1_3 smallPairClosure_42 smallPairLarge_42
    smallPairSieve_1_3 smallPairSieve_1_3_valid ?_
    smallPairSeeds_42_checked smallPairClosure_42_checked smallPairFilter_42_checked
    smallPairNoTriangle_42_checked t ht hpair hlarge hbound hneA hneB
  intro q hq
  rw [seedRootDisk_1_3_eq, List.mem_toFinset] at hq
  exact hq

end D1Bound5
end
