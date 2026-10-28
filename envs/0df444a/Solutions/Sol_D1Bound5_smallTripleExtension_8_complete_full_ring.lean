-- Prove2me | solution 1 for D1Bound5.smallTripleExtension_8_complete_full_ring
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:48:17.486631+00:00
-- url     : https://prove2.me/submissions/811a67b2-c1a8-4cfa-8a44-04fc4ef0631a

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
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_DiskEnumeration_Definitions
import Definitions.Def_D1Bound5_PairExtensionCore_Definitions
import Definitions.Def_D1Bound5_PairSeedDisks_Definitions
import Definitions.Def_D1Bound5_SmallTripleExtensionData8_Definitions
import Definitions.Def_D1Bound5_SquareTest_Definitions
import Theorems.Thm_D1Bound5_QuadInt_hasSquareRoot_iff
import Theorems.Thm_D1Bound5_pairClosure_complete_full_ring
import Theorems.Thm_D1Bound5_pairClosure_of_checked
import Theorems.Thm_D1Bound5_pairSeedsCovered_of_checked
import Theorems.Thm_D1Bound5_seedRootDisk_1_1_eq
import Theorems.Thm_D1Bound5_smallTripleClosure_8_checked
import Theorems.Thm_D1Bound5_smallTripleFilter_8_checked
import Theorems.Thm_D1Bound5_smallTripleSeeds_8_checked
import Theorems.Thm_D1Bound5_tripleExtensionFilter_of_checked

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt















/-- Complete radius-10^40 extension list for manuscript row 8. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (e : QuadInt 1 1 ≃+* 𝓞 K) (z : QuadInt 1 1)
    (hpair : PairExtension smallTripleAnchorA_8 smallTripleAnchorB_8 z)
    (hthird : ∃ r, r*r = smallTripleAnchorC_8*z+1)
    (hz : z ≠ 0) (ha : z ≠ smallTripleAnchorA_8)
    (hb : z ≠ smallTripleAnchorB_8) (hc : z ≠ smallTripleAnchorC_8)
    (hNz : z.norm ≤ 10^80) :
    z ∈ smallTripleAllowed_8 := by
  have hpos : 0 < discriminant 1 1 := by decide
  have hroot : ∃ r0, r0*r0 = smallTripleAnchorA_8*smallTripleAnchorB_8+1 :=
    (hasSquareRoot_iff hpos _).1 (by decide +kernel)
  have hmem : z ∈ smallTriplePairClosure_8 := by
    apply pairClosure_complete_full_ring hK phi hpos e smallTripleAnchorA_8 smallTripleAnchorB_8
      (by decide) (by decide) (by decide) hroot (by decide) (by decide)
      (10^80) smallTriplePairClosure_8 ?_ ?_ z hpair hNz
    · intro x hx hNx
      apply pairSeedsCovered_of_checked hpos smallTripleAnchorA_8 smallTripleAnchorB_8
        (by decide) (by decide) seedRootDisk_1_1 smallTriplePairClosure_8
        ?_ smallTripleSeeds_8_checked x hx hNx
      intro q hq
      rw [seedRootDisk_1_1_eq, List.mem_toFinset] at hq
      exact hq
    · intro x hx w hw hNw
      exact pairClosure_of_checked smallTripleAnchorA_8 smallTripleAnchorB_8 (10^80)
        smallTriplePairClosure_8 smallTripleClosure_8_checked hx hw hNw
  exact tripleExtensionFilter_of_checked hpos smallTripleAnchorA_8 smallTripleAnchorB_8 smallTripleAnchorC_8
    smallTriplePairClosure_8 smallTripleAllowed_8 smallTripleFilter_8_checked
    hmem hz ha hb hc hthird





end D1Bound5
end
