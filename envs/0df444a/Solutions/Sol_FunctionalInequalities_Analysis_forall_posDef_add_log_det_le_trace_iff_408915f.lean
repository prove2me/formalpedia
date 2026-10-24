-- Prove2me | solution 1 for FunctionalInequalities.Analysis.forall_posDef_add_log_det_le_trace_iff_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:20:55.530418+00:00
-- url     : https://prove2.me/submissions/02922afc-0420-47b9-8b6e-297ca0972f15

import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.Trace

noncomputable section
open Matrix
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section LogDetInf
private lemma FunctionalInequalities.Analysis.log_det_add_card_le_trace {n : ℕ}
    {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosDef) :
    Real.log M.det + n ≤ M.trace := by
  rw [hM.isHermitian.det_eq_prod_eigenvalues,
    hM.isHermitian.trace_eq_sum_eigenvalues]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  rw [Real.log_prod (fun i _ => ne_of_gt (hM.eigenvalues_pos i))]
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => Real.log_le_sub_one_of_pos (hM.eigenvalues_pos i))
  simpa only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, le_sub_iff_add_le] using h
private lemma FunctionalInequalities.Analysis.exists_posDef_square {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) :
    ∃ B : Matrix (Fin n) (Fin n) ℝ, B.PosDef ∧ B * B = A := by
  let e := Unitary.conjStarAlgAut ℝ (Matrix (Fin n) (Fin n) ℝ)
    hA.isHermitian.eigenvectorUnitary
  let B := e (diagonal (fun i => Real.sqrt (hA.isHermitian.eigenvalues i)))
  have hp : B.PosDef := by
    dsimp only [B, e]
    rw [Unitary.conjStarAlgAut_apply]
    exact (Matrix.IsUnit.posDef_star_right_conjugate_iff Unitary.isUnit_coe).mpr
      (Matrix.posDef_diagonal_iff.mpr
        (fun i => Real.sqrt_pos.mpr (hA.eigenvalues_pos i)))
  refine ⟨B, hp, ?_⟩
  change e _ * e _ = A
  rw [← map_mul, Matrix.diagonal_mul_diagonal]
  simp only [Real.mul_self_sqrt (le_of_lt (hA.eigenvalues_pos _))]
  simpa only [Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using
    hA.isHermitian.spectral_theorem.symm
private lemma FunctionalInequalities.Analysis.posDef_of_forall_log_det_le_trace {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) (b : ℝ)
    (H : ∀ J : Matrix (Fin n) (Fin n) ℝ,
      J.PosDef → b + Real.log J.det + n ≤ (J * A).trace) :
    A.PosDef := by
  let e := Unitary.conjStarAlgAut ℝ (Matrix (Fin n) (Fin n) ℝ)
    hA.isHermitian.eigenvectorUnitary
  have hs : A = e (diagonal hA.isHermitian.eigenvalues) := by
    simpa only [Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using
      hA.isHermitian.spectral_theorem
  have hd (d : Fin n → ℝ) (hp : ∀ i, 0 < d i) :
      b + Real.log (∏ i, d i) + n ≤
        ∑ i, d i * hA.isHermitian.eigenvalues i := by
    have hj : (e (diagonal d)).PosDef := by
      dsimp only [e]
      rw [Unitary.conjStarAlgAut_apply]
      exact (Matrix.IsUnit.posDef_star_right_conjugate_iff Unitary.isUnit_coe).mpr
        (Matrix.posDef_diagonal_iff.mpr hp)
    have ht : (e (diagonal d) * A).trace =
        ∑ i, d i * hA.isHermitian.eigenvalues i := by
      conv_lhs => rw [hs]
      rw [← map_mul, Matrix.trace_map, Matrix.diagonal_mul_diagonal,
        Matrix.trace_diagonal]
    simpa only [Matrix.det_map, Matrix.det_diagonal, ht] using H _ hj
  apply hA.isHermitian.posDef_iff_eigenvalues_pos.mpr
  intro i
  by_contra hi
  have hz : hA.isHermitian.eigenvalues i = 0 :=
    le_antisymm (le_of_not_gt hi) (hA.eigenvalues_nonneg i)
  let t := Real.exp ((∑ j, hA.isHermitian.eigenvalues j) - b + 1)
  have hp (j : Fin n) : 0 < (if i = j then t else 1) := by
    split_ifs
    · exact Real.exp_pos _
    · norm_num
  have h := hd (fun j => if i = j then t else 1) hp
  have he (j : Fin n) :
      (if i = j then t else 1) * hA.isHermitian.eigenvalues j =
        hA.isHermitian.eigenvalues j := by
    by_cases hij : i = j <;> simp only [hij, ite_true, ite_false, one_mul]
    subst j
    simp only [hz, mul_zero]
  simp only [he, Finset.prod_ite_eq, Finset.mem_univ, if_true, t, Real.log_exp] at h
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- **`log det` as an infimum of linear functions** (used for the distributional Monge–Ampère trace
inequality): for a positive semidefinite `A` and real `b`,
`(∀ J ≻ 0, b + log det J + n ≤ tr(J A)) ↔ (A ≻ 0 ∧ e^b ≤ det A)`. -/
theorem solution {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (b : ℝ) :
    (∀ J : Matrix (Fin n) (Fin n) ℝ, J.PosDef → b + Real.log J.det + n ≤ (J * A).trace) ↔
      (A.PosDef ∧ Real.exp b ≤ A.det) := by
  constructor
  · intro H
    have hpos := posDef_of_forall_log_det_le_trace hA b H
    refine ⟨hpos, ?_⟩
    have h := H A⁻¹ hpos.inv
    rw [Matrix.nonsing_inv_mul A
        ((Matrix.isUnit_iff_isUnit_det A).mp hpos.isUnit),
      Matrix.trace_one, Fintype.card_fin, Matrix.det_nonsing_inv,
      Ring.inverse_eq_inv, Real.log_inv] at h
    apply (Real.le_log_iff_exp_le hpos.det_pos).mp
    linarith
  · rintro ⟨hpos, hb⟩ J hJ
    obtain ⟨B, hB, hBB⟩ := exists_posDef_square hpos
    have hstar : star B = B := by
      rw [Matrix.star_eq_conjTranspose, hB.isHermitian.eq]
    have hM : (B * J * B).PosDef := by
      simpa only [hstar] using
        (Matrix.IsUnit.posDef_star_right_conjugate_iff hB.isUnit).mpr hJ
    have htr : (B * J * B).trace = (J * A).trace := by
      rw [Matrix.trace_mul_cycle, hBB, Matrix.trace_mul_comm]
    have hdet : (B * J * B).det = J.det * A.det := by
      rw [Matrix.det_mul, Matrix.det_mul, ← hBB, Matrix.det_mul]
      ring
    have h := log_det_add_card_le_trace hM
    rw [htr, hdet,
      Real.log_mul (ne_of_gt hJ.det_pos) (ne_of_gt hpos.det_pos)] at h
    have hlog := (Real.le_log_iff_exp_le hpos.det_pos).mpr hb
    linarith
