-- Prove2me | solution 1 for D1Bound5.full_ring_finitePRowForm_exists_one_le_norm
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:37:09.083962+00:00
-- url     : https://prove2.me/submissions/dbaaf73a-72ff-495d-b0df-bdda57b2daed

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FinitePIntegralRows_Definitions
import Definitions.Def_D1Bound5_FinitePMatrix_Definitions
import Theorems.Thm_D1Bound5_full_ring_finitePDividedMatrix_det_ne_zero
import Theorems.Thm_D1Bound5_one_le_norm_integer

section
open scoped NumberField
open Module

namespace D1Bound5









@[simp] theorem map_finitePDividedMatrix {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a b s c : R) (i j : Fin 4) :
    f (finitePDividedMatrix a b s c i j) =
      finitePDividedMatrix (f a) (f b) (f s) (f c) i j := by
  fin_cases i <;> fin_cases j <;>
    simp [finitePDividedMatrix,finitePRConstant,finitePTConstant,
      finitePRLeft,finitePRRight,finitePTLeft,finitePTRight,finitePairQuadratic,
      finitePRLeftCoeff,finitePRRightCoeff,finitePTLeftCoeff,finitePTRightCoeff, map_ofNat]









@[simp] theorem map_finitePRowForm {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a b s c z rA rB rS : R) (i : Fin 4) :
    f (finitePRowForm a b s c z rA rB rS i) =
      finitePRowForm (f a) (f b) (f s) (f c) (f z) (f rA) (f rB) (f rS) i := by
  simp only [finitePRowForm,Matrix.mulVec,dotProduct,map_sum,map_mul,map_finitePDividedMatrix]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  fin_cases j <;> rfl

/-- A genuine full-ring integral row has norm at least one. Both the
nonsingularity and the integrality of this constructed P matrix are proved
here; they are not supplied as separate approximation certificates. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a b s c z rA rB rS : 𝓞 K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hs : s ≠ 0)
    (hab : a ≠ b) (has : a ≠ s) (hbs : b ≠ s) (hz : z ≠ 0)
    (hAB : ‖phi (a : K)‖ ≤ ‖phi (b : K)‖)
    (hBS : ‖phi (b : K)‖ ≤ ‖phi (s : K)‖)
    (hC : 200*‖phi (s : K)‖ ≤ ‖phi (c : K)‖) :
    ∃ i : Fin 4, 1 ≤ ‖finitePRowForm (phi (a : K)) (phi (b : K)) (phi (s : K))
      (phi (c : K)) (phi (z : K)) (phi (rA : K)) (phi (rB : K)) (phi (rS : K)) i‖ := by
  classical
  let f : 𝓞 K →+* ℂ := phi.comp (algebraMap (𝓞 K) K)
  have hf : Function.Injective f := by
    intro x y hxy
    apply NumberField.RingOfIntegers.ext
    exact phi.injective hxy
  have hz0 : f z ≠ 0 := by
    intro h
    exact hz (hf (by simpa only [map_zero] using h))
  let M := finitePDividedMatrix (f a) (f b) (f s) (f c)
  let v : Fin 4 → ℂ := ![f z,f rA,f rB,f rS]
  have hdet : M.det ≠ 0 := full_ring_finitePDividedMatrix_det_ne_zero hK phi a b s c
    ha hb hs hab has hbs hAB hBS hC
  have hu : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).2 (isUnit_iff_ne_zero.mpr hdet)
  have hi : Function.Injective M.mulVec := Matrix.mulVec_injective_iff_isUnit.2 hu
  have hex : ∃ i : Fin 4, finitePRowForm (f a) (f b) (f s) (f c)
      (f z) (f rA) (f rB) (f rS) i ≠ 0 := by
    by_contra h
    push_neg at h
    have hzero : M.mulVec v = 0 := by funext i; exact h i
    have hv : v = 0 := hi (by simpa using hzero)
    exact hz0 (by simpa [v] using congrFun hv (0 : Fin 4))
  obtain ⟨i,hi⟩ := hex
  let L := finitePRowForm a b s c z rA rB rS i
  have hL : f L = finitePRowForm (f a) (f b) (f s) (f c) (f z) (f rA) (f rB) (f rS) i :=
    map_finitePRowForm f _ _ _ _ _ _ _ _ i
  have hL0 : L ≠ 0 := by
    intro hzero
    apply hi
    rw [← hL,hzero,map_zero]
  have hbnd := one_le_norm_integer hK phi hL0
  change 1 ≤ ‖f L‖ at hbnd
  rw [hL] at hbnd
  exact ⟨i,hbnd⟩

end D1Bound5
end
