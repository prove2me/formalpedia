-- Prove2me | solution 1 for D1Bound5.smallTripleExtension_10_complete_full_ring
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:49:27.270991+00:00
-- url     : https://prove2.me/submissions/ec82c948-cce3-44cc-bfff-492c99771758

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
import Definitions.Def_D1Bound5_SmallTripleExtensionData10_Definitions
import Definitions.Def_D1Bound5_SquareTest_Definitions
import Theorems.Thm_D1Bound5_QuadInt_hasSquareRoot_iff
import Theorems.Thm_D1Bound5_pairClosure_complete_full_ring
import Theorems.Thm_D1Bound5_pairClosure_of_checked
import Theorems.Thm_D1Bound5_pairSeedsCovered_of_checked
import Theorems.Thm_D1Bound5_seedRootDisk_1_2_eq
import Theorems.Thm_D1Bound5_smallTripleClosure_10_checked
import Theorems.Thm_D1Bound5_smallTripleFilter_10_checked
import Theorems.Thm_D1Bound5_smallTripleSeeds_10_checked
import Theorems.Thm_D1Bound5_tripleExtensionFilter_of_checked

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt



















/-- Complete radius-10^40 extension list for manuscript row 10. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (e : QuadInt 1 2 ≃+* 𝓞 K) (z : QuadInt 1 2)
    (hpair : PairExtension smallTripleAnchorA_10 smallTripleAnchorB_10 z)
    (hthird : ∃ r, r*r = smallTripleAnchorC_10*z+1)
    (hz : z ≠ 0) (ha : z ≠ smallTripleAnchorA_10)
    (hb : z ≠ smallTripleAnchorB_10) (hc : z ≠ smallTripleAnchorC_10)
    (hNz : z.norm ≤ 10^80) :
    z ∈ smallTripleAllowed_10 := by
  have hpos : 0 < discriminant 1 2 := by decide
  have hroot : ∃ r0, r0*r0 = smallTripleAnchorA_10*smallTripleAnchorB_10+1 :=
    (hasSquareRoot_iff hpos _).1 (by decide +kernel)
  have hmem : z ∈ smallTriplePairClosure_10 := by
    apply pairClosure_complete_full_ring hK phi hpos e smallTripleAnchorA_10 smallTripleAnchorB_10
      (by decide) (by decide) (by decide) hroot (by decide) (by decide)
      (10^80) smallTriplePairClosure_10 ?_ ?_ z hpair hNz
    · intro x hx hNx
      apply pairSeedsCovered_of_checked hpos smallTripleAnchorA_10 smallTripleAnchorB_10
        (by decide) (by decide) seedRootDisk_1_2 smallTriplePairClosure_10
        ?_ smallTripleSeeds_10_checked x hx hNx
      intro q hq
      rw [seedRootDisk_1_2_eq, List.mem_toFinset] at hq
      exact hq
    · intro x hx w hw hNw
      exact pairClosure_of_checked smallTripleAnchorA_10 smallTripleAnchorB_10 (10^80)
        smallTriplePairClosure_10 smallTripleClosure_10_checked hx hw hNw
  exact tripleExtensionFilter_of_checked hpos smallTripleAnchorA_10 smallTripleAnchorB_10 smallTripleAnchorC_10
    smallTriplePairClosure_10 smallTripleAllowed_10 smallTripleFilter_10_checked
    hmem hz ha hb hc hthird

end D1Bound5
end
