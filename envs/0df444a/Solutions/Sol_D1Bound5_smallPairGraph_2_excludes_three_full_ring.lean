-- Prove2me | solution 1 for D1Bound5.smallPairGraph_2_excludes_three_full_ring
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:33:46.265446+00:00
-- url     : https://prove2.me/submissions/c8ee0f8f-e937-4334-a533-be946f662299

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
import Definitions.Def_D1Bound5_SmallPairGraphData2_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphData2_Definitions_002
import Definitions.Def_D1Bound5_SmallPairSieve_0_1_Definitions
import Definitions.Def_D1Bound5_SquareTest_Definitions
import Theorems.Thm_D1Bound5_PairLightPrepared2_left_checked
import Theorems.Thm_D1Bound5_PairLightPrepared2_right_checked
import Theorems.Thm_D1Bound5_QuadInt_hasSquareRoot_iff
import Theorems.Thm_D1Bound5_pairGraphTriangleFreeBool_of_split
import Theorems.Thm_D1Bound5_seedRootDisk_0_1_eq
import Theorems.Thm_D1Bound5_smallPairClosure_2_checked
import Theorems.Thm_D1Bound5_smallPairFilter_2_checked
import Theorems.Thm_D1Bound5_smallPairSeeds_2_checked
import Theorems.Thm_D1Bound5_smallPairSieve_0_1_valid
import Theorems.Thm_D1Bound5_small_pair_graph_excludes_three_full_ring

section
/- Preserved body from D1Bound5.SmallPairGraphInputs2; original SHA256 05c6eac538f8497cd3a821770526ca8706d00a25abdc81b4c26cfd4d1fb29b57. -/

namespace D1Bound5
set_option maxRecDepth 100000

open QuadInt








namespace PairGraphPrepared2



end PairGraphPrepared2
end D1Bound5

/- Preserved body from D1Bound5.SmallPairGraphArithmetic2; original SHA256 26154516f673902cc1e3bce80054f0c96e08d80a543d1e1f2882f177302acaf7. -/

namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0







end D1Bound5

/- Preserved body from D1Bound5.SmallPairGraphWitnessData2; original SHA256 f319a0bdaefa48f1a9f3ae5ceb65656c94c041b0fa290e14cab6856d8341c7fb. -/

namespace D1Bound5.PairGraphPrepared2
set_option maxRecDepth 100000









end D1Bound5.PairGraphPrepared2

/- Preserved body from D1Bound5.SmallPairGraphClosure2; original SHA256 6c3d39e00759e54ecfe739fe7c0b0c438ed702899f4932797158545d8d3f914b. -/

namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared2





end D1Bound5

/- Preserved body from D1Bound5.SmallPairRawSelectedData2; original SHA256 bd14d335ba3742940ee6255966b2aa93923682ac39e18375e9a9ee7870d1dc4f. -/

namespace D1Bound5.PairSelectedPrepared2
set_option maxRecDepth 100000









end D1Bound5.PairSelectedPrepared2

/- Preserved body from D1Bound5.SmallPairLightAssembly2; original SHA256 28e25096d2fda97cfe2f853e3f3dc8734674d85d678e091170cdd16eaf988ed7. -/

namespace D1Bound5.PairLightPrepared2
set_option maxRecDepth 100000
set_option maxHeartbeats 0



















end D1Bound5.PairLightPrepared2

/- Preserved body from D1Bound5.SmallPairGraphTriangle2; original SHA256 304600336a461f07462df8aa2968c65908970f7e5cd79d6981f86853f6ac6e7d. -/

namespace D1Bound5
set_option maxRecDepth 100000

theorem smallPairNoTriangle_2_checked :
    pairGraphTriangleFreeBool smallPairSieve_0_1 smallPairLarge_2 = true :=
  pairGraphTriangleFreeBool_of_split smallPairSieve_0_1 smallPairLarge_2 PairGraphPrepared2.colors
    PairLightPrepared2.left_checked PairLightPrepared2.right_checked

end D1Bound5

/- Preserved body from D1Bound5.SmallPairGraphData2; original SHA256 89e5d1cc4246d5ec20132684b3f2d13a6ac263401e770195eef0c09fa478e927. -/
end

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt

/-- Complete large-extension triangle exclusion for pair-table row 2. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (e : QuadInt 0 1 ≃+* 𝓞 K) (t : Fin 3 → QuadInt 0 1)
    (ht : IsD1Tuple t)
    (hpair : ∀ i, PairExtension smallPairA_2 smallPairB_2 (t i))
    (hlarge : ∀ i, 9 ≤ (t i).norm) (hbound : ∀ i, (t i).norm ≤ 10^1100)
    (hneA : ∀ i, t i ≠ smallPairA_2) (hneB : ∀ i, t i ≠ smallPairB_2) : False := by
  have hpos : 0 < discriminant 0 1 := by decide
  have hroot : ∃ r0, r0*r0 = smallPairA_2*smallPairB_2+1 :=
    (hasSquareRoot_iff hpos _).1 (by decide +kernel)
  apply small_pair_graph_excludes_three_full_ring hK phi hpos e smallPairA_2 smallPairB_2
    (by decide) (by decide) (by decide) hroot (by decide) (by decide)
    (10^1100) seedRootDisk_0_1 smallPairClosure_2 smallPairLarge_2
    smallPairSieve_0_1 smallPairSieve_0_1_valid ?_
    smallPairSeeds_2_checked smallPairClosure_2_checked smallPairFilter_2_checked
    smallPairNoTriangle_2_checked t ht hpair hlarge hbound hneA hneB
  intro q hq
  rw [seedRootDisk_0_1_eq, List.mem_toFinset] at hq
  exact hq





end D1Bound5
end
