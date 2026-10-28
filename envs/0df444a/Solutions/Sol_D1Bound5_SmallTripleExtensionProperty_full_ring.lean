-- Prove2me | solution 1 for D1Bound5.SmallTripleExtensionProperty.full_ring
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:33:37.46341+00:00
-- url     : https://prove2.me/submissions/a7f3a50c-3d24-422e-bbf6-a980a976fe09

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
import Theorems.Thm_D1Bound5_ProperCommonExtension_map_equiv
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg
import Theorems.Thm_D1Bound5_norm_sq_full_ring_equiv

section
open scoped NumberField Classical
open Module

namespace D1Bound5
open QuadInt

/-- Transfer both finite-extension consequences from integer coordinates
to the actual full ring through its proved ring equivalence. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    {tau nu : ℤ} (e : QuadInt tau nu ≃+* 𝓞 K) (phi : K →+* ℂ)
    (A : Finset (QuadInt tau nu)) (hA : SmallTripleExtensionProperty A) :
    (∀ z : 𝓞 K, ProperCommonExtension (A.image e) z →
      ‖phi (z : K)‖^2 ≤ (10 : ℝ)^80 → ‖phi (z : K)‖ < 85) ∧
    (∀ z w : 𝓞 K, ProperCommonExtension (A.image e) z →
      ProperCommonExtension (A.image e) w →
      ‖phi (z : K)‖^2 ≤ (10 : ℝ)^80 →
      ‖phi (w : K)‖^2 ≤ (10 : ℝ)^80 → z = w) := by
  classical
  have himage : (A.image e).image e.symm = A := by
    simp [Finset.image_image, Function.comp_def]
  have hproper (z : 𝓞 K) (hz : ProperCommonExtension (A.image e) z) :
      ProperCommonExtension A (e.symm z) := by
    have h := ProperCommonExtension.map_equiv e.symm (A.image e) z hz
    rwa [himage] at h
  have hnorm (z : 𝓞 K) :
      ‖phi (z : K)‖^2 = ((e.symm z).norm : ℝ) := by
    simpa only [RingEquiv.apply_symm_apply] using
      norm_sq_full_ring_equiv e phi (e.symm z)
  have hbound (z : 𝓞 K) (hz : ‖phi (z : K)‖^2 ≤ (10 : ℝ)^80) :
      (e.symm z).norm ≤ 10^80 := by
    rw [hnorm z] at hz
    exact_mod_cast hz
  constructor
  · intro z hz hNz
    have hN := hA.1 (e.symm z) (hproper z hz) (hbound z hNz)
    have hNr : ((e.symm z).norm : ℝ) < (85 : ℝ)^2 := by exact_mod_cast hN
    nlinarith only [hnorm z, hNr, _root_.norm_nonneg (phi (z : K))]
  · intro z w hz hw hNz hNw
    apply e.symm.injective
    exact hA.2 (e.symm z) (e.symm w) (hproper z hz) (hproper w hw)
      (hbound z hNz) (hbound w hNw)



end D1Bound5
end
