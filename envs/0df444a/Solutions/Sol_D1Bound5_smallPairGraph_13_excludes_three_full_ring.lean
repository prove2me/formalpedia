-- Prove2me | solution 1 for D1Bound5.smallPairGraph_13_excludes_three_full_ring
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:33:38.444263+00:00
-- url     : https://prove2.me/submissions/a0d9d087-ac35-415d-afbe-23fa94b2bcfd

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
import Definitions.Def_D1Bound5_SmallPairGraphData13_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphData13_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphData13_Definitions_003
import Definitions.Def_D1Bound5_SmallPairGraphData13_Definitions_004
import Definitions.Def_D1Bound5_SmallPairSieve_0_2_Definitions
import Definitions.Def_D1Bound5_SquareTest_Definitions
import Theorems.Thm_D1Bound5_PairLightPrepared13_left_checked
import Theorems.Thm_D1Bound5_PairLightPrepared13_right_checked
import Theorems.Thm_D1Bound5_QuadInt_hasSquareRoot_iff
import Theorems.Thm_D1Bound5_pairGraphTriangleFreeBool_of_split
import Theorems.Thm_D1Bound5_seedRootDisk_0_2_eq
import Theorems.Thm_D1Bound5_smallPairClosure_13_checked
import Theorems.Thm_D1Bound5_smallPairFilter_13_checked
import Theorems.Thm_D1Bound5_smallPairSeeds_13_checked
import Theorems.Thm_D1Bound5_smallPairSieve_0_2_valid
import Theorems.Thm_D1Bound5_small_pair_graph_excludes_three_full_ring

section
/- Preserved body from D1Bound5.SmallPairGraphInputs13; original SHA256 c5e162c4bc960250e92b15dd3d783468d049132d96b85979af9506d77a521f61. -/

namespace D1Bound5
set_option maxRecDepth 100000

open QuadInt








namespace PairGraphPrepared13



end PairGraphPrepared13
end D1Bound5

/- Preserved body from D1Bound5.SmallPairGraphArithmetic13; original SHA256 65049f6bec9c79d86936bd3deea19ec925d693c7048de9fb9e32c5bbcecaaa7e. -/

namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0







end D1Bound5

/- Preserved body from D1Bound5.SmallPairGraphWitnessData13; original SHA256 556060a6b394aa67f85deaa77b5ff08b8016b064b2322a52df284b5ef8ed4787. -/

namespace D1Bound5.PairGraphPrepared13
set_option maxRecDepth 100000









end D1Bound5.PairGraphPrepared13

/- Preserved body from D1Bound5.SmallPairGraphClosure13; original SHA256 81e59ccaa6115a892462e75edc02ea7716dfe2ceae2a7cdb305c8fad43165cad. -/

namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared13





end D1Bound5

/- Preserved body from D1Bound5.SmallPairRawSelectedData13; original SHA256 c7a93e661ec2ce8824b6a499d24999a58d69a9e9ad5fac8fb832f9193941ad55. -/

namespace D1Bound5.PairSelectedPrepared13
set_option maxRecDepth 100000









end D1Bound5.PairSelectedPrepared13

/- Preserved body from D1Bound5.SmallPairLightAssembly13; original SHA256 e76013453eff7aaa9f79d4c825325e8205e5a5479ec026372abb2ecc94fc4549. -/

namespace D1Bound5.PairLightPrepared13
set_option maxRecDepth 100000
set_option maxHeartbeats 0



















end D1Bound5.PairLightPrepared13

/- Preserved body from D1Bound5.SmallPairGraphTriangle13; original SHA256 486dda3838b12341918f0571b2caa08b7fd29d98208b269f2b8d10573b84da87. -/

namespace D1Bound5
set_option maxRecDepth 100000

theorem smallPairNoTriangle_13_checked :
    pairGraphTriangleFreeBool smallPairSieve_0_2 smallPairLarge_13 = true :=
  pairGraphTriangleFreeBool_of_split smallPairSieve_0_2 smallPairLarge_13 PairGraphPrepared13.colors
    PairLightPrepared13.left_checked PairLightPrepared13.right_checked

end D1Bound5

/- Preserved body from D1Bound5.SmallPairGraphData13; original SHA256 12a849f4683eb3969e097c63c91d9f00719653bc181140cfce7f1a09a576ea58. -/
end

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt

/-- Complete large-extension triangle exclusion for pair-table row 13. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (e : QuadInt 0 2 ≃+* 𝓞 K) (t : Fin 3 → QuadInt 0 2)
    (ht : IsD1Tuple t)
    (hpair : ∀ i, PairExtension smallPairA_13 smallPairB_13 (t i))
    (hlarge : ∀ i, 9 ≤ (t i).norm) (hbound : ∀ i, (t i).norm ≤ 10^1100)
    (hneA : ∀ i, t i ≠ smallPairA_13) (hneB : ∀ i, t i ≠ smallPairB_13) : False := by
  have hpos : 0 < discriminant 0 2 := by decide
  have hroot : ∃ r0, r0*r0 = smallPairA_13*smallPairB_13+1 :=
    (hasSquareRoot_iff hpos _).1 (by decide +kernel)
  apply small_pair_graph_excludes_three_full_ring hK phi hpos e smallPairA_13 smallPairB_13
    (by decide) (by decide) (by decide) hroot (by decide) (by decide)
    (10^1100) seedRootDisk_0_2 smallPairClosure_13 smallPairLarge_13
    smallPairSieve_0_2 smallPairSieve_0_2_valid ?_
    smallPairSeeds_13_checked smallPairClosure_13_checked smallPairFilter_13_checked
    smallPairNoTriangle_13_checked t ht hpair hlarge hbound hneA hneB
  intro q hq
  rw [seedRootDisk_0_2_eq, List.mem_toFinset] at hq
  exact hq

end D1Bound5
end
