-- Prove2me | solution 1 for D1Bound5.smallTripleRepresentative_6_property
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:24:18.223309+00:00
-- url     : https://prove2.me/submissions/9e3deb7b-a8e5-4894-9c0e-e64c9808a78f

import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_SmallExtensionSymmetry_Definitions
import Definitions.Def_D1Bound5_SmallTripleExtensionData6_Definitions
import Theorems.Thm_D1Bound5_QuadInt_norm_formula
import Theorems.Thm_D1Bound5_smallTripleExtension_6_complete_full_ring

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt

private theorem smallTripleExtensionProperty_of_list {tau nu : ℤ}
    (A : Finset (QuadInt tau nu)) (allowed : List (QuadInt tau nu))
    (hcomplete : ∀ z, ProperCommonExtension A z → z.norm ≤ 10^80 → z ∈ allowed)
    (hbound : ∀ z ∈ allowed, z.norm < 85^2)
    (hunique : ∀ z ∈ allowed, ∀ w ∈ allowed, z = w) :
    SmallTripleExtensionProperty A := by
  constructor
  · intro z hz hNz
    exact hbound z (hcomplete z hz hNz)
  · intro z w hz hw hNz hNw
    exact hunique z (hcomplete z hz hNz) w (hcomplete w hw hNw)











/-- Both finite-extension consequences for manuscript representative 6. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (e : QuadInt 1 1 ≃+* 𝓞 K) :
    SmallTripleExtensionProperty
      {smallTripleAnchorA_6, smallTripleAnchorB_6, smallTripleAnchorC_6} := by
  apply smallTripleExtensionProperty_of_list _ smallTripleAllowed_6
  · intro z hz hNz
    exact smallTripleExtension_6_complete_full_ring hK phi e z
      ⟨hz.2.2 _ (by simp), hz.2.2 _ (by simp)⟩
      (hz.2.2 _ (by simp)) hz.1
      (fun h => hz.2.1 (by simp [h]))
      (fun h => hz.2.1 (by simp [h]))
      (fun h => hz.2.1 (by simp [h])) hNz
  · norm_num [smallTripleAllowed_6, QuadInt.norm_formula]
  · simp [smallTripleAllowed_6]









end D1Bound5
end
