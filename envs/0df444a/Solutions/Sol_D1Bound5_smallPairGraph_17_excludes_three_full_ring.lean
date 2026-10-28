-- Prove2me | solution 1 for D1Bound5.smallPairGraph_17_excludes_three_full_ring
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:33:40.330188+00:00
-- url     : https://prove2.me/submissions/00bd7b28-776a-436c-93d1-85f5ea9b690c

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs17_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs17_Definitions_002
import Definitions.Def_D1Bound5_SmallPairSieve_0_2_Definitions
import Definitions.Def_D1Bound5_SquareTest_Definitions
import Theorems.Thm_D1Bound5_PairLightPrepared17_left_checked
import Theorems.Thm_D1Bound5_PairLightPrepared17_right_checked
import Theorems.Thm_D1Bound5_QuadInt_hasSquareRoot_iff
import Theorems.Thm_D1Bound5_pairGraphTriangleFreeBool_of_split
import Theorems.Thm_D1Bound5_seedRootDisk_0_2_eq
import Theorems.Thm_D1Bound5_smallPairClosure_17_checked
import Theorems.Thm_D1Bound5_smallPairFilter_17_checked
import Theorems.Thm_D1Bound5_smallPairSeeds_17_checked
import Theorems.Thm_D1Bound5_smallPairSieve_0_2_valid
import Theorems.Thm_D1Bound5_small_pair_graph_excludes_three_full_ring

section
namespace D1Bound5
set_option maxRecDepth 100000

theorem smallPairNoTriangle_17_checked :
    pairGraphTriangleFreeBool smallPairSieve_0_2 smallPairLarge_17 = true :=
  pairGraphTriangleFreeBool_of_split smallPairSieve_0_2 smallPairLarge_17 PairGraphPrepared17.colors
    PairLightPrepared17.left_checked PairLightPrepared17.right_checked

end D1Bound5
end
section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt

/-- Complete large-extension triangle exclusion for pair-table row 17. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (e : QuadInt 0 2 ≃+* 𝓞 K) (t : Fin 3 → QuadInt 0 2)
    (ht : IsD1Tuple t)
    (hpair : ∀ i, PairExtension smallPairA_17 smallPairB_17 (t i))
    (hlarge : ∀ i, 9 ≤ (t i).norm) (hbound : ∀ i, (t i).norm ≤ 10^1100)
    (hneA : ∀ i, t i ≠ smallPairA_17) (hneB : ∀ i, t i ≠ smallPairB_17) : False := by
  have hpos : 0 < discriminant 0 2 := by decide
  have hroot : ∃ r0, r0*r0 = smallPairA_17*smallPairB_17+1 :=
    (hasSquareRoot_iff hpos _).1 (by decide +kernel)
  apply small_pair_graph_excludes_three_full_ring hK phi hpos e smallPairA_17 smallPairB_17
    (by decide) (by decide) (by decide) hroot (by decide) (by decide)
    (10^1100) seedRootDisk_0_2 smallPairClosure_17 smallPairLarge_17
    smallPairSieve_0_2 smallPairSieve_0_2_valid ?_
    smallPairSeeds_17_checked smallPairClosure_17_checked smallPairFilter_17_checked
    smallPairNoTriangle_17_checked t ht hpair hlarge hbound hneA hneB
  intro q hq
  rw [seedRootDisk_0_2_eq, List.mem_toFinset] at hq
  exact hq

end D1Bound5
end

