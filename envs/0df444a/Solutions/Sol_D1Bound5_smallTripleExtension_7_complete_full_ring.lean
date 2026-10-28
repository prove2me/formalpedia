-- Prove2me | solution 1 for D1Bound5.smallTripleExtension_7_complete_full_ring
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:48:29.763564+00:00
-- url     : https://prove2.me/submissions/df7ec1e8-3621-462e-b6c8-c464d30e7b1f

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
import Definitions.Def_D1Bound5_SmallTripleExtensionData7_Definitions
import Definitions.Def_D1Bound5_SquareTest_Definitions
import Theorems.Thm_D1Bound5_QuadInt_hasSquareRoot_iff
import Theorems.Thm_D1Bound5_pairClosure_complete_full_ring
import Theorems.Thm_D1Bound5_pairClosure_of_checked
import Theorems.Thm_D1Bound5_pairSeedsCovered_of_checked
import Theorems.Thm_D1Bound5_seedRootDisk_1_1_eq
import Theorems.Thm_D1Bound5_smallTripleClosure_7_checked
import Theorems.Thm_D1Bound5_smallTripleFilter_7_checked
import Theorems.Thm_D1Bound5_smallTripleSeeds_7_checked
import Theorems.Thm_D1Bound5_tripleExtensionFilter_of_checked

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt













/-- Complete radius-10^40 extension list for manuscript row 7. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (e : QuadInt 1 1 ≃+* 𝓞 K) (z : QuadInt 1 1)
    (hpair : PairExtension smallTripleAnchorA_7 smallTripleAnchorB_7 z)
    (hthird : ∃ r, r*r = smallTripleAnchorC_7*z+1)
    (hz : z ≠ 0) (ha : z ≠ smallTripleAnchorA_7)
    (hb : z ≠ smallTripleAnchorB_7) (hc : z ≠ smallTripleAnchorC_7)
    (hNz : z.norm ≤ 10^80) :
    z ∈ smallTripleAllowed_7 := by
  have hpos : 0 < discriminant 1 1 := by decide
  have hroot : ∃ r0, r0*r0 = smallTripleAnchorA_7*smallTripleAnchorB_7+1 :=
    (hasSquareRoot_iff hpos _).1 (by decide +kernel)
  have hmem : z ∈ smallTriplePairClosure_7 := by
    apply pairClosure_complete_full_ring hK phi hpos e smallTripleAnchorA_7 smallTripleAnchorB_7
      (by decide) (by decide) (by decide) hroot (by decide) (by decide)
      (10^80) smallTriplePairClosure_7 ?_ ?_ z hpair hNz
    · intro x hx hNx
      apply pairSeedsCovered_of_checked hpos smallTripleAnchorA_7 smallTripleAnchorB_7
        (by decide) (by decide) seedRootDisk_1_1 smallTriplePairClosure_7
        ?_ smallTripleSeeds_7_checked x hx hNx
      intro q hq
      rw [seedRootDisk_1_1_eq, List.mem_toFinset] at hq
      exact hq
    · intro x hx w hw hNw
      exact pairClosure_of_checked smallTripleAnchorA_7 smallTripleAnchorB_7 (10^80)
        smallTriplePairClosure_7 smallTripleClosure_7_checked hx hw hNw
  exact tripleExtensionFilter_of_checked hpos smallTripleAnchorA_7 smallTripleAnchorB_7 smallTripleAnchorC_7
    smallTriplePairClosure_7 smallTripleAllowed_7 smallTripleFilter_7_checked
    hmem hz ha hb hc hthird







end D1Bound5
end
