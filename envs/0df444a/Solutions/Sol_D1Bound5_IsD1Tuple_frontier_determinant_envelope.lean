-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.frontier_determinant_envelope
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:28:56.816271+00:00
-- url     : https://prove2.me/submissions/40a31508-7b21-429a-96f8-9ab2a25e7cad

import Lean.Util.CollectAxioms
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_DeterminantNormalization_Definitions
import Definitions.Def_D1Bound5_FrontierRootBounds_Definitions
import Definitions.Def_D1Bound5_FrontierScalarReduction_Definitions
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_ReferenceMatrixSpectral_Definitions
import Definitions.Def_D1Bound5_RootMatrixOperatorBound_Definitions
import Theorems.Thm_D1Bound5_IsD1Tuple_exists_symmetric_root_matrix
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg
import Theorems.Thm_D1Bound5_exists_frontier_symmetric_root_matrix
import Theorems.Thm_D1Bound5_four_zero_diagonal_operator_norm_lt
import Theorems.Thm_D1Bound5_frontier_mixed_matrix_bounds
import Theorems.Thm_D1Bound5_frontier_mixed_rankOne_upper
import Theorems.Thm_D1Bound5_full_ring_scaledRootMatrix_det_norm_lower
import Theorems.Thm_D1Bound5_halfOffDiagonalInverse_norm
import Theorems.Thm_D1Bound5_normalizedRootError_diag
import Theorems.Thm_D1Bound5_reference_perturbed_det_ne_zero

section
open scoped NumberField Matrix.Norms.L2Operator BigOperators
open Matrix Module

namespace D1Bound5

/-- The actual scaled integral determinant obeys the complete frontier
envelope, with constants evaluated at any positive lower bounds alpha,beta
having alpha<=beta and alpha*beta>=5. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 4 → 𝓞 K) (ha : IsD1Tuple a)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖))
    (alpha beta : ℝ) (halpha : 0 < alpha) (hbeta : 0 < beta)
    (halphabeta : alpha ≤ beta) (hprod : 5 ≤ alpha*beta)
    (hA : alpha ≤ ‖phi (a 0 : K)‖) (hB : beta ≤ ‖phi (a 1 : K)‖) :
    let A := ‖phi (a 0 : K)‖
    let B := ‖phi (a 1 : K)‖
    let C := ‖phi (a 2 : K)‖
    let D := ‖phi (a 3 : K)‖
    A*B*C*D ≤ 2*frontierK alpha beta*(A^2+B^2+C^2+D^2)+
      frontierL alpha beta*(A*B+A*C+A*D+B*C+B*D+C*D)+frontierQ alpha beta := by
  classical
  let f : 𝓞 K →+* ℂ := phi.comp (algebraMap (𝓞 K) K)
  let w : Fin 4 → ℂ := fun i => f (a i)
  let k : ℝ := 1/2+1/(7*alpha*beta)
  let l : ℝ := 1/2+1/(7*beta^2)
  have hb (i : Fin 4) (hi : i ≠ 0) : beta ≤ ‖w i‖ :=
    hB.trans (hmon (by omega : (1 : Fin 4) ≤ i))
  have hfirstProd (i j : Fin 4) (hij : i ≠ j) (hzero : i = 0 ∨ j = 0) :
      alpha*beta ≤ ‖f (a i)*f (a j)‖ := by
    rw [norm_mul]
    rcases hzero with rfl | rfl
    · exact mul_le_mul hA (hb j hij.symm) hbeta.le (norm_nonneg _)
    · calc
        alpha*beta ≤ ‖f (a 0)‖*‖f (a i)‖ :=
          mul_le_mul hA (hb i hij) hbeta.le (norm_nonneg _)
        _ = ‖f (a i)‖*‖f (a 0)‖ := mul_comm _ _
  have hlaterProd (i j : Fin 4) (hzero : ¬(i = 0 ∨ j = 0)) :
      beta^2 ≤ ‖f (a i)*f (a j)‖ := by
    rw [norm_mul, pow_two]
    exact mul_le_mul (hb i (fun h => hzero (Or.inl h)))
      (hb j (fun h => hzero (Or.inr h))) hbeta.le (norm_nonneg _)
  have hbetaSq : alpha*beta ≤ beta^2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr halphabeta) hbeta.le]
  have hlarge (i j : Fin 4) (hij : i ≠ j) : 5 ≤ ‖f (a i)*f (a j)‖ := by
    by_cases hzero : i = 0 ∨ j = 0
    · exact hprod.trans (hfirstProd i j hij hzero)
    · exact hprod.trans (hbetaSq.trans (hlaterProd i j hzero))
  have hl : (1/2 : ℝ) ≤ l := by
    have hpos : 0 ≤ 1/(7*beta^2) := by positivity
    dsimp [l]
    linarith only [hpos]
  have hlk : l ≤ k := by
    have hdiv : 1/(7*beta^2) ≤ 1/(7*alpha*beta) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith only [hbetaSq]
    dsimp [k,l]
    linarith only [hdiv]
  obtain ⟨M,hdiag,hsym,hroot⟩ := ha.exists_symmetric_root_matrix a
  have hex (i : Fin 4) : ∃ z : ℂ, z^2 = f (a i) :=
    IsAlgClosed.exists_pow_nat_eq (f (a i)) (by decide : 0 < 2)
  choose u hu using hex
  obtain ⟨S,hd,hs,hsq,hgood⟩ :=
    exists_frontier_symmetric_root_matrix f a u M hu hdiag hsym hroot hlarge
  let F := normalizedRootError w u (S.map f)
  have hzero (i : Fin 4) : F i i = 0 :=
    normalizedRootError_diag w u (S.map f) hu (fun j => congrArg f (hd j)) i
  have hsymF (i j : Fin 4) : F i j = F j i := by
    change u i*f (S i j)*u j-f (a i)*f (a j) =
      u j*f (S j i)*u i-f (a j)*f (a i)
    rw [hs i j]
    ring
  have herr (i j : Fin 4) (hij : i ≠ j) :
      ‖F i j-(1/2 : ℂ)‖ ≤ 1/(7*‖f (a i)*f (a j)‖) := hgood i j hij
  have hfirst (i j : Fin 4) (hij : i ≠ j) (hij0 : i = 0 ∨ j = 0) :
      ‖F i j-(1/2 : ℂ)‖ ≤ k-1/2 := by
    have hp := hfirstProd i j hij hij0
    have hp0 : 0 < ‖f (a i)*f (a j)‖ := (mul_pos halpha hbeta).trans_le hp
    have hdiv : 1/(7*‖f (a i)*f (a j)‖) ≤ 1/(7*alpha*beta) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith only [hp]
    dsimp [k]
    linarith only [herr i j hij, hdiv]
  have hlater (i j : Fin 4) (hij : i ≠ j) (hij0 : ¬(i = 0 ∨ j = 0)) :
      ‖F i j-(1/2 : ℂ)‖ ≤ l-1/2 := by
    have hp := hlaterProd i j hij0
    have hp0 : 0 < ‖f (a i)*f (a j)‖ := (sq_pos_of_pos hbeta).trans_le hp
    have hdiv : 1/(7*‖f (a i)*f (a j)‖) ≤ 1/(7*beta^2) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith only [hp]
    dsimp [l]
    linarith only [herr i j hij, hdiv]
  obtain ⟨hdet,hG⟩ := frontier_mixed_matrix_bounds F k l hl hlk hzero hsymF hfirst hlater
  have hEzero (i : Fin 4) : (F-halfOffDiagonal) i i = 0 := by
    simp [Matrix.sub_apply, halfOffDiagonal, hzero]
  have hEoff (i j : Fin 4) (hij : i ≠ j) :
      ‖(F-halfOffDiagonal) i j‖ < (1/30 : ℝ) := by
    have hp := hlarge i j hij
    have hp0 : 0 < ‖f (a i)*f (a j)‖ := by linarith only [hp]
    have hdiv : 1/(7*‖f (a i)*f (a j)‖) ≤ (1/35 : ℝ) := by
      apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
      nlinarith only [hp]
    simp only [Matrix.sub_apply, halfOffDiagonal, if_neg hij]
    linarith only [herr i j hij, hdiv]
  have hE := four_zero_diagonal_operator_norm_lt (F-halfOffDiagonal) (1/30)
    (by norm_num) hEzero hEoff
  have hF : F.det ≠ 0 := by
    apply reference_perturbed_det_ne_zero F
    have hmul := Matrix.l2_opNorm_mul halfOffDiagonalInverse (F-halfOffDiagonal)
    rw [halfOffDiagonalInverse_norm] at hmul
    linarith only [hmul,hE]
  have hupper := frontier_mixed_rankOne_upper F w (k^2*l) (9*k^2*l^2) hF hdet hG
  have hmatrix : F+Matrix.vecMulVec w w = scaledRootMatrix u (S.map f) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.vecMulVec_apply,
      F, w, normalizedRootError, scaledRootMatrix, Matrix.map_apply]
    ring
  have hlower := full_ring_scaledRootMatrix_det_norm_lower hK phi
    (by decide : Even (Fintype.card (Fin 4))) a S hd hsq u hu
  have hlower' : ‖w 0‖*‖w 1‖*‖w 2‖*‖w 3‖ ≤ ‖(F+Matrix.vecMulVec w w).det‖ := by
    rw [hmatrix]
    convert hlower using 1
    simp [w, f, Fin.prod_univ_four]
  have h := hlower'.trans hupper
  simpa only [w, f, RingHom.comp_apply, frontierK, frontierL, frontierQ, k, l] using h



end D1Bound5
end
