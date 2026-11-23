-- Prove2me | solution 1 for Formalism.L2.LamCM.hadamardInequality
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:04:56.970299+00:00
-- url     : https://prove2.me/submissions/a4d8d266-fa4f-458f-92d4-244bdc245ed4

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ProdMulLeDetIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors ComplexOrder
namespace Formalism.L2.LamCM
theorem _root_.solution : HadamardPD := by
  intro m A hA
  have hdpos : ∀ i, 0 < (A i i).re := fun i => by
    simpa using (Complex.lt_def.1 (hA.diag_pos (i := i))).1
  have hdiag : ∀ i, A i i = ((A i i).re : ℂ) := fun i => (hA.isHermitian.coe_re_apply_self i).symm
  set s : Fin m → ℝ := fun i => (Real.sqrt (A i i).re)⁻¹ with hs
  have hspos : ∀ i, 0 < s i := fun i => inv_pos.2 (Real.sqrt_pos.2 (hdpos i))
  have hs2 : ∀ i, s i ^ 2 * (A i i).re = 1 := fun i => by
    rw [hs]; simp only
    rw [inv_pow, Real.sq_sqrt (hdpos i).le, inv_mul_cancel₀ (hdpos i).ne']
  set D : Matrix (Fin m) (Fin m) ℂ := Matrix.diagonal fun i => (s i : ℂ) with hD
  have hDh : D.conjTranspose = D := by
    rw [hD, Matrix.diagonal_conjTranspose]
    congr 1
    ext i
    simp
  have hDdet : D.det = ∏ i, (s i : ℂ) := by rw [hD, Matrix.det_diagonal]
  have hDu : IsUnit D := by
    rw [Matrix.isUnit_iff_isUnit_det, hDdet]
    exact IsUnit.mk0 _ (Finset.prod_ne_zero_iff.2 fun i _ => by exact_mod_cast (hspos i).ne')
  have hC : (D.conjTranspose * A * D).PosDef := hA.conjTranspose_mul_mul_same (Matrix.mulVec_injective_iff_isUnit.2 hDu)
  set C := D.conjTranspose * A * D with hCdef
  have hCii : ∀ i, C i i = 1 := fun i => by
    rw [hCdef, hDh, hD]
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
    rw [hdiag i]
    rw [show (s i : ℂ) * ((A i i).re : ℂ) * (s i : ℂ) = ((s i ^ 2 * (A i i).re : ℝ) : ℂ) by push_cast; ring, hs2 i]
    simp
  have hCdet : C.det = A.det * ∏ i, ((s i ^ 2 : ℝ) : ℂ) := by
    rw [hCdef, Matrix.det_mul, Matrix.det_mul, hDh, hDdet]
    push_cast
    rw [Finset.prod_pow]
    ring
  have hev := hC.isHermitian.det_eq_prod_eigenvalues
  have htr := hC.isHermitian.trace_eq_sum_eigenvalues
  set ev := hC.isHermitian.eigenvalues with hev_def
  have hevpos : ∀ i, 0 < ev i := hC.eigenvalues_pos
  have hsum : ∑ i, ev i = m := by
    have : C.trace = (m : ℂ) := by
      simp [Matrix.trace, hCii]
    rw [this] at htr
    apply Complex.ofReal_injective
    push_cast
    exact htr.symm
  have hprod : ∏ i, ev i ≤ 1 := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simp
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have amgm := Real.geom_mean_le_arith_mean Finset.univ (fun _ => (1 : ℝ)) ev
      (fun _ _ => zero_le_one) (by simp [hmR]) (fun i _ => (hevpos i).le)
    simp only [Real.rpow_one, one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one, hsum, div_self hmR.ne'] at amgm
    by_contra hlt
    push Not at hlt
    have := Real.one_lt_rpow hlt (inv_pos.2 hmR)
    linarith
  have hA' : A.det = (∏ i, ev i : ℝ) * ∏ i, (((A i i).re : ℝ) : ℂ) := by
    have h1 : C.det = ((∏ i, ev i : ℝ) : ℂ) := by rw [hev]; push_cast; rfl
    have h2 : (∏ i, ((s i ^ 2 : ℝ) : ℂ)) * ∏ i, (((A i i).re : ℝ) : ℂ) = 1 := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_eq_one
      intro i _
      rw [← Complex.ofReal_mul, hs2 i, Complex.ofReal_one]
    calc A.det = A.det * ((∏ i, ((s i ^ 2 : ℝ) : ℂ)) * ∏ i, (((A i i).re : ℝ) : ℂ)) := by rw [h2, mul_one]
      _ = C.det * ∏ i, (((A i i).re : ℝ) : ℂ) := by rw [hCdet]; ring
      _ = _ := by rw [h1]
  rw [hA', ← Complex.ofReal_prod, ← Complex.ofReal_mul, Complex.ofReal_re]
  calc (∏ i, ev i) * ∏ i, (A i i).re ≤ 1 * ∏ i, (A i i).re :=
        mul_le_mul_of_nonneg_right hprod (Finset.prod_nonneg fun i _ => (hdpos i).le)
    _ = _ := one_mul _
end Formalism.L2.LamCM
