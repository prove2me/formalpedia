-- Prove2me | solution 1 for D1Bound5.smallTripleExtension_6_complete_full_ring
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:48:31.296433+00:00
-- url     : https://prove2.me/submissions/d1943272-2ce9-4b18-b0d7-d4dd9d8f54f9

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
import Definitions.Def_D1Bound5_SmallTripleExtensionData6_Definitions
import Definitions.Def_D1Bound5_SquareTest_Definitions
import Theorems.Thm_D1Bound5_QuadInt_hasSquareRoot_iff
import Theorems.Thm_D1Bound5_pairClosure_complete_full_ring
import Theorems.Thm_D1Bound5_pairClosure_of_checked
import Theorems.Thm_D1Bound5_pairSeedsCovered_of_checked
import Theorems.Thm_D1Bound5_seedRootDisk_1_1_eq
import Theorems.Thm_D1Bound5_smallTripleClosure_6_checked
import Theorems.Thm_D1Bound5_smallTripleFilter_6_checked
import Theorems.Thm_D1Bound5_smallTripleSeeds_6_checked
import Theorems.Thm_D1Bound5_tripleExtensionFilter_of_checked

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt











/-- Complete radius-10^40 extension list for manuscript row 6. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (e : QuadInt 1 1 ≃+* 𝓞 K) (z : QuadInt 1 1)
    (hpair : PairExtension smallTripleAnchorA_6 smallTripleAnchorB_6 z)
    (hthird : ∃ r, r*r = smallTripleAnchorC_6*z+1)
    (hz : z ≠ 0) (ha : z ≠ smallTripleAnchorA_6)
    (hb : z ≠ smallTripleAnchorB_6) (hc : z ≠ smallTripleAnchorC_6)
    (hNz : z.norm ≤ 10^80) :
    z ∈ smallTripleAllowed_6 := by
  have hpos : 0 < discriminant 1 1 := by decide
  have hroot : ∃ r0, r0*r0 = smallTripleAnchorA_6*smallTripleAnchorB_6+1 :=
    (hasSquareRoot_iff hpos _).1 (by decide +kernel)
  have hmem : z ∈ smallTriplePairClosure_6 := by
    apply pairClosure_complete_full_ring hK phi hpos e smallTripleAnchorA_6 smallTripleAnchorB_6
      (by decide) (by decide) (by decide) hroot (by decide) (by decide)
      (10^80) smallTriplePairClosure_6 ?_ ?_ z hpair hNz
    · intro x hx hNx
      apply pairSeedsCovered_of_checked hpos smallTripleAnchorA_6 smallTripleAnchorB_6
        (by decide) (by decide) seedRootDisk_1_1 smallTriplePairClosure_6
        ?_ smallTripleSeeds_6_checked x hx hNx
      intro q hq
      rw [seedRootDisk_1_1_eq, List.mem_toFinset] at hq
      exact hq
    · intro x hx w hw hNw
      exact pairClosure_of_checked smallTripleAnchorA_6 smallTripleAnchorB_6 (10^80)
        smallTriplePairClosure_6 smallTripleClosure_6_checked hx hw hNw
  exact tripleExtensionFilter_of_checked hpos smallTripleAnchorA_6 smallTripleAnchorB_6 smallTripleAnchorC_6
    smallTriplePairClosure_6 smallTripleAllowed_6 smallTripleFilter_6_checked
    hmem hz ha hb hc hthird









end D1Bound5
end
