-- Prove2me | solution 1 for D1Bound5.full_ring_productFive_arithmetic_growth
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:54:32.415772+00:00
-- url     : https://prove2.me/submissions/c6c25274-2526-4133-bfe2-f235acd7164e

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_DeterminantNormalization_Definitions
import Definitions.Def_D1Bound5_ProductFiveArithmeticClosure_Definitions
import Definitions.Def_D1Bound5_ProductFiveMatrixBridge_Definitions
import Definitions.Def_D1Bound5_ProductFiveRankTwo_Definitions
import Theorems.Thm_D1Bound5_five_normalized_root_det
import Theorems.Thm_D1Bound5_five_root_det_ne_zero_of_schur
import Theorems.Thm_D1Bound5_one_le_norm_integer

section
open scoped NumberField BigOperators Matrix.Norms.L2Operator
open Matrix Module

namespace D1Bound5







/-- Arithmetic final step of product-five in the full ring of integers
of every imaginary quadratic field. Only the two explicit analytic Schur
estimates remain as hypotheses; nonsingularity of the integral determinant
is derived, not assumed. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 5 → 𝓞 K) (M : Matrix (Fin 5) (Fin 5) (𝓞 K))
    (u : Fin 5 → ℂ)
    (hu : ∀ i, (u i)^2 = phi (a i : K))
    (hdiag : ∀ i, M i i = a i)
    (hsym : ∀ i j, M i j = M j i)
    (hd : fiveLastValue (fun i => phi (a i : K)) ≠ 0)
    (hGne : (fiveNormalizedSchur
        (fun i => phi (a i : K)) u
        (M.map (phi.comp (algebraMap (𝓞 K) K)))).det ≠ 0)
    (hGlt : ‖(fiveNormalizedSchur
        (fun i => phi (a i : K)) u
        (M.map (phi.comp (algebraMap (𝓞 K) K)))).det‖ < (1/3 : ℝ)) :
    3 * (∏ i : Fin 4, ‖phi (a (Fin.castAdd 1 i) : K)‖) <
      ‖phi (a 4 : K)‖ := by
  let f : 𝓞 K →+* ℂ := phi.comp (algebraMap (𝓞 K) K)
  let t : Fin 5 → ℂ := fun i => f (a i)
  let N : Matrix (Fin 5) (Fin 5) ℂ := M.map f
  let G := fiveNormalizedSchur t u N
  let d := fiveLastValue t
  have hd' : d ≠ 0 := hd
  have hdn : 0 < ‖d‖ := norm_pos_iff.mpr hd'
  have hdiag' : ∀ i, N i i = t i := by
    intro i
    simp [N, t, Matrix.map_apply, hdiag]
  have hsym' : Nᵀ = N := by
    ext i j
    change f (M j i) = f (M i j)
    rw [hsym]
  have hN : N.det ≠ 0 :=
    five_root_det_ne_zero_of_schur t u N hu hdiag' hsym' hd' hGne
  have hM : M.det ≠ 0 := by
    intro hm
    apply hN
    have hh := RingHom.map_det f M
    change f M.det = (M.map f).det at hh
    rw [← hh, hm, map_zero]
  have hinter : 1 ≤ ‖f M.det‖ := by
    simpa [f] using one_le_norm_integer hK phi hM
  have hid := five_normalized_root_det t u N hu hdiag' hsym' hd'
  change (∏ i, t i) * N.det = d^2 * G.det at hid
  have hmap : f M.det = N.det := by
    simpa [N] using RingHom.map_det f M
  have hnormid :
      (∏ i, ‖t i‖) * ‖f M.det‖ = ‖d‖^2 * ‖G.det‖ := by
    rw [← hmap] at hid
    have hh := congrArg norm hid
    simpa only [norm_mul, norm_prod, norm_pow] using hh
  have hnonneg : 0 ≤ (∏ i, ‖t i‖) := by positivity
  have hprod :
      (∏ i, ‖t i‖) ≤ ‖d‖^2 * ‖G.det‖ := by
    calc
      (∏ i, ‖t i‖) ≤ (∏ i, ‖t i‖) * ‖f M.det‖ :=
        le_mul_of_one_le_right hnonneg hinter
      _ = _ := hnormid
  have hsmall : (∏ i, ‖t i‖) < ‖d‖^2 / 3 := by
    calc
      _ ≤ ‖d‖^2 * ‖G.det‖ := hprod
      _ < ‖d‖^2 * (1/3 : ℝ) :=
        mul_lt_mul_of_pos_left hGlt (pow_pos hdn _)
      _ = ‖d‖^2 / 3 := by ring
  have hprodfive :
      (∏ i, ‖t i‖) =
        (∏ i : Fin 4, ‖t (Fin.castAdd 1 i)‖) * ‖d‖ := by
    simp only [Fin.prod_univ_five, Fin.prod_univ_four]
    change ‖t 0‖ * ‖t 1‖ * ‖t 2‖ * ‖t 3‖ * ‖t 4‖ =
      (‖t 0‖ * ‖t 1‖ * ‖t 2‖ * ‖t 3‖) * ‖d‖
    rfl
  rw [hprodfive] at hsmall
  have hfinal :
      3 * (∏ i : Fin 4, ‖t (Fin.castAdd 1 i)‖) < ‖d‖ := by
    have hx : 3 * (∏ i : Fin 4, ‖t (Fin.castAdd 1 i)‖) * ‖d‖ <
        ‖d‖ * ‖d‖ := by nlinarith only [hsmall]
    by_contra hbad
    have hh : ‖d‖ ≤ 3 * (∏ i : Fin 4, ‖t (Fin.castAdd 1 i)‖) :=
      le_of_not_gt hbad
    have hmul := mul_le_mul_of_nonneg_right hh hdn.le
    nlinarith only [hx, hmul]
  simpa [t, f, d, fiveLastValue] using hfinal



end D1Bound5
end
