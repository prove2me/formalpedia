-- Prove2me | solution 1 for D1Bound5.smallPairGraph_31_excludes_three_full_ring
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:33:49.532387+00:00
-- url     : https://prove2.me/submissions/33e845af-ca7f-4e0d-89b0-d95535dbc62b

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs31_Definitions
import Definitions.Def_D1Bound5_SmallPairSieve_0_5_Definitions
import Definitions.Def_D1Bound5_SquareTest_Definitions
import Definitions.Def_D1Bound5_TwoSmallSeedDisks_Definitions
import Theorems.Thm_D1Bound5_QuadInt_hasSquareRoot_iff
import Theorems.Thm_D1Bound5_seedRootDisk_0_5_eq
import Theorems.Thm_D1Bound5_smallPairClosure_31_checked
import Theorems.Thm_D1Bound5_smallPairFilter_31_checked
import Theorems.Thm_D1Bound5_smallPairNoTriangle_31_checked
import Theorems.Thm_D1Bound5_smallPairSeeds_31_checked
import Theorems.Thm_D1Bound5_smallPairSieve_0_5_valid
import Theorems.Thm_D1Bound5_small_pair_graph_excludes_three_full_ring

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt

/-- Complete large-extension triangle exclusion for pair-table row 31. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (e : QuadInt 0 5 ≃+* 𝓞 K) (t : Fin 3 → QuadInt 0 5)
    (ht : IsD1Tuple t)
    (hpair : ∀ i, PairExtension smallPairA_31 smallPairB_31 (t i))
    (hlarge : ∀ i, 9 ≤ (t i).norm) (hbound : ∀ i, (t i).norm ≤ 10^1100)
    (hneA : ∀ i, t i ≠ smallPairA_31) (hneB : ∀ i, t i ≠ smallPairB_31) : False := by
  have hpos : 0 < discriminant 0 5 := by decide
  have hroot : ∃ r0, r0*r0 = smallPairA_31*smallPairB_31+1 :=
    (hasSquareRoot_iff hpos _).1 (by decide +kernel)
  apply small_pair_graph_excludes_three_full_ring hK phi hpos e smallPairA_31 smallPairB_31
    (by decide) (by decide) (by decide) hroot (by decide) (by decide)
    (10^1100) seedRootDisk_0_5 smallPairClosure_31 smallPairLarge_31
    smallPairSieve_0_5 smallPairSieve_0_5_valid ?_
    smallPairSeeds_31_checked smallPairClosure_31_checked smallPairFilter_31_checked
    smallPairNoTriangle_31_checked t ht hpair hlarge hbound hneA hneB
  intro q hq
  rw [seedRootDisk_0_5_eq, List.mem_toFinset] at hq
  exact hq

end D1Bound5
end
