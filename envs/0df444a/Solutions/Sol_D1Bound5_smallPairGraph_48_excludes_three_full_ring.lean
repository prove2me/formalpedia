-- Prove2me | solution 1 for D1Bound5.smallPairGraph_48_excludes_three_full_ring
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:33:44.519935+00:00
-- url     : https://prove2.me/submissions/396fde99-2c79-4d2d-94b5-3795eeb0162f

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs48_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs48_Definitions_002
import Definitions.Def_D1Bound5_SmallPairSieve_1_8_Definitions
import Definitions.Def_D1Bound5_SquareTest_Definitions
import Definitions.Def_D1Bound5_TwoSmallSeedDisks_Definitions
import Theorems.Thm_D1Bound5_PairLightPrepared48_left_checked
import Theorems.Thm_D1Bound5_PairLightPrepared48_right_checked
import Theorems.Thm_D1Bound5_QuadInt_hasSquareRoot_iff
import Theorems.Thm_D1Bound5_pairGraphTriangleFreeBool_of_split
import Theorems.Thm_D1Bound5_seedRootDisk_1_8_eq
import Theorems.Thm_D1Bound5_smallPairClosure_48_checked
import Theorems.Thm_D1Bound5_smallPairFilter_48_checked
import Theorems.Thm_D1Bound5_smallPairSeeds_48_checked
import Theorems.Thm_D1Bound5_smallPairSieve_1_8_valid
import Theorems.Thm_D1Bound5_small_pair_graph_excludes_three_full_ring

section
namespace D1Bound5
set_option maxRecDepth 100000

theorem smallPairNoTriangle_48_checked :
    pairGraphTriangleFreeBool smallPairSieve_1_8 smallPairLarge_48 = true :=
  pairGraphTriangleFreeBool_of_split smallPairSieve_1_8 smallPairLarge_48 PairGraphPrepared48.colors
    PairLightPrepared48.left_checked PairLightPrepared48.right_checked

end D1Bound5
end
section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt

/-- Complete large-extension triangle exclusion for pair-table row 48. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (e : QuadInt 1 8 ≃+* 𝓞 K) (t : Fin 3 → QuadInt 1 8)
    (ht : IsD1Tuple t)
    (hpair : ∀ i, PairExtension smallPairA_48 smallPairB_48 (t i))
    (hlarge : ∀ i, 9 ≤ (t i).norm) (hbound : ∀ i, (t i).norm ≤ 10^1100)
    (hneA : ∀ i, t i ≠ smallPairA_48) (hneB : ∀ i, t i ≠ smallPairB_48) : False := by
  have hpos : 0 < discriminant 1 8 := by decide
  have hroot : ∃ r0, r0*r0 = smallPairA_48*smallPairB_48+1 :=
    (hasSquareRoot_iff hpos _).1 (by decide +kernel)
  apply small_pair_graph_excludes_three_full_ring hK phi hpos e smallPairA_48 smallPairB_48
    (by decide) (by decide) (by decide) hroot (by decide) (by decide)
    (10^1100) seedRootDisk_1_8 smallPairClosure_48 smallPairLarge_48
    smallPairSieve_1_8 smallPairSieve_1_8_valid ?_
    smallPairSeeds_48_checked smallPairClosure_48_checked smallPairFilter_48_checked
    smallPairNoTriangle_48_checked t ht hpair hlarge hbound hneA hneB
  intro q hq
  rw [seedRootDisk_1_8_eq, List.mem_toFinset] at hq
  exact hq

end D1Bound5
end

