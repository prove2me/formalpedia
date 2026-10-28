-- Prove2me | solution 1 for D1Bound5.smallTripleExtension_5_complete_full_ring
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:49:35.516479+00:00
-- url     : https://prove2.me/submissions/28b6c9f6-49e7-472a-a05a-15a3526e3d7d

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
import Definitions.Def_D1Bound5_SmallTripleExtensionData5_Definitions
import Definitions.Def_D1Bound5_SquareTest_Definitions
import Theorems.Thm_D1Bound5_QuadInt_hasSquareRoot_iff
import Theorems.Thm_D1Bound5_pairClosure_complete_full_ring
import Theorems.Thm_D1Bound5_pairClosure_of_checked
import Theorems.Thm_D1Bound5_pairSeedsCovered_of_checked
import Theorems.Thm_D1Bound5_seedRootDisk_0_2_eq
import Theorems.Thm_D1Bound5_smallTripleClosure_5_checked
import Theorems.Thm_D1Bound5_smallTripleFilter_5_checked
import Theorems.Thm_D1Bound5_smallTripleSeeds_5_checked
import Theorems.Thm_D1Bound5_tripleExtensionFilter_of_checked

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt









/-- Complete radius-10^40 extension list for manuscript row 5. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (e : QuadInt 0 2 ≃+* 𝓞 K) (z : QuadInt 0 2)
    (hpair : PairExtension smallTripleAnchorA_5 smallTripleAnchorB_5 z)
    (hthird : ∃ r, r*r = smallTripleAnchorC_5*z+1)
    (hz : z ≠ 0) (ha : z ≠ smallTripleAnchorA_5)
    (hb : z ≠ smallTripleAnchorB_5) (hc : z ≠ smallTripleAnchorC_5)
    (hNz : z.norm ≤ 10^80) :
    z ∈ smallTripleAllowed_5 := by
  have hpos : 0 < discriminant 0 2 := by decide
  have hroot : ∃ r0, r0*r0 = smallTripleAnchorA_5*smallTripleAnchorB_5+1 :=
    (hasSquareRoot_iff hpos _).1 (by decide +kernel)
  have hmem : z ∈ smallTriplePairClosure_5 := by
    apply pairClosure_complete_full_ring hK phi hpos e smallTripleAnchorA_5 smallTripleAnchorB_5
      (by decide) (by decide) (by decide) hroot (by decide) (by decide)
      (10^80) smallTriplePairClosure_5 ?_ ?_ z hpair hNz
    · intro x hx hNx
      apply pairSeedsCovered_of_checked hpos smallTripleAnchorA_5 smallTripleAnchorB_5
        (by decide) (by decide) seedRootDisk_0_2 smallTriplePairClosure_5
        ?_ smallTripleSeeds_5_checked x hx hNx
      intro q hq
      rw [seedRootDisk_0_2_eq, List.mem_toFinset] at hq
      exact hq
    · intro x hx w hw hNw
      exact pairClosure_of_checked smallTripleAnchorA_5 smallTripleAnchorB_5 (10^80)
        smallTriplePairClosure_5 smallTripleClosure_5_checked hx hw hNw
  exact tripleExtensionFilter_of_checked hpos smallTripleAnchorA_5 smallTripleAnchorB_5 smallTripleAnchorC_5
    smallTriplePairClosure_5 smallTripleAllowed_5 smallTripleFilter_5_checked
    hmem hz ha hb hc hthird











end D1Bound5
end
