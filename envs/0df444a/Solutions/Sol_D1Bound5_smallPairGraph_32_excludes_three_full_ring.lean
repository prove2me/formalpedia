-- Prove2me | solution 1 for D1Bound5.smallPairGraph_32_excludes_three_full_ring
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:33:29.616202+00:00
-- url     : https://prove2.me/submissions/0a2ab6c3-4355-4665-8b04-7cadf8d11b83

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs32_Definitions
import Definitions.Def_D1Bound5_SmallPairSieve_0_6_Definitions
import Definitions.Def_D1Bound5_SquareTest_Definitions
import Definitions.Def_D1Bound5_TwoSmallSeedDisks_Definitions
import Theorems.Thm_D1Bound5_QuadInt_hasSquareRoot_iff
import Theorems.Thm_D1Bound5_seedRootDisk_0_6_eq
import Theorems.Thm_D1Bound5_smallPairClosure_32_checked
import Theorems.Thm_D1Bound5_smallPairFilter_32_checked
import Theorems.Thm_D1Bound5_smallPairNoTriangle_32_checked
import Theorems.Thm_D1Bound5_smallPairSeeds_32_checked
import Theorems.Thm_D1Bound5_smallPairSieve_0_6_valid
import Theorems.Thm_D1Bound5_small_pair_graph_excludes_three_full_ring

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt

/-- Complete large-extension triangle exclusion for pair-table row 32. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (e : QuadInt 0 6 ≃+* 𝓞 K) (t : Fin 3 → QuadInt 0 6)
    (ht : IsD1Tuple t)
    (hpair : ∀ i, PairExtension smallPairA_32 smallPairB_32 (t i))
    (hlarge : ∀ i, 9 ≤ (t i).norm) (hbound : ∀ i, (t i).norm ≤ 10^1100)
    (hneA : ∀ i, t i ≠ smallPairA_32) (hneB : ∀ i, t i ≠ smallPairB_32) : False := by
  have hpos : 0 < discriminant 0 6 := by decide
  have hroot : ∃ r0, r0*r0 = smallPairA_32*smallPairB_32+1 :=
    (hasSquareRoot_iff hpos _).1 (by decide +kernel)
  apply small_pair_graph_excludes_three_full_ring hK phi hpos e smallPairA_32 smallPairB_32
    (by decide) (by decide) (by decide) hroot (by decide) (by decide)
    (10^1100) seedRootDisk_0_6 smallPairClosure_32 smallPairLarge_32
    smallPairSieve_0_6 smallPairSieve_0_6_valid ?_
    smallPairSeeds_32_checked smallPairClosure_32_checked smallPairFilter_32_checked
    smallPairNoTriangle_32_checked t ht hpair hlarge hbound hneA hneB
  intro q hq
  rw [seedRootDisk_0_6_eq, List.mem_toFinset] at hq
  exact hq

end D1Bound5
end
