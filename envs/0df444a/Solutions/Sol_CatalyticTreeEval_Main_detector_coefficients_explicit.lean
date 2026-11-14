-- Prove2me | solution 1 for CatalyticTreeEval.Main.detector_coefficients_explicit
-- status  : ACCEPTED   (prove)
-- author  : @sragavan
-- created : 2026-11-14T02:59:10.621229+00:00
-- url     : https://prove2.me/submissions/45cd23cf-98ee-41e5-b63d-464be5fee394

import Definitions.Def_CatalyticTreeEval_DetectorCoefficients

set_option autoImplicit false

namespace CatalyticTreeEval.Main

private theorem binomialMatrix_det (p q : ℕ) : (binomialMatrix p q).det = 1 := by
  classical
  have htri : (binomialMatrix p q).IsLowerTriangular := by
    intro i j hij
    simp [binomialMatrix, Nat.choose_eq_zero_of_lt (show i.val < j.val from hij)]
  rw [Matrix.det_of_isLowerTriangular _ htri]
  simp [binomialMatrix]


end CatalyticTreeEval.Main



namespace CatalyticTreeEval.Main

private theorem alternating_choose_sum (p n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), (-1 : ZMod p) ^ j * (n.choose j : ZMod p)) =
      if n = 0 then 1 else 0 := by
  have h := congrArg (Int.castRingHom (ZMod p)) (Int.alternating_sum_range_choose (n := n))
  simpa only [map_sum, map_mul, map_pow, map_neg, map_one, map_natCast, apply_ite, map_zero] using h

private theorem binomial_inverse_kernel (p n r : ℕ) :
    (∑ j ∈ Finset.range (n + 1), (n.choose j : ZMod p) *
      (if r ≤ j then (-1 : ZMod p) ^ (j - r) * (j.choose r : ZMod p) else 0)) =
      if n = r then 1 else 0 := by
  classical
  by_cases hr : r ≤ n
  · rw [show n + 1 = r + (n - r + 1) by omega, Finset.sum_range_add]
    have hzero : (∑ j ∈ Finset.range r, (n.choose j : ZMod p) *
        (if r ≤ j then (-1 : ZMod p) ^ (j - r) * (j.choose r : ZMod p) else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [if_neg (by simpa using (Finset.mem_range.mp hj).not_ge), mul_zero]
    rw [hzero, zero_add]
    have hterm (j : ℕ) : (n.choose (r + j) : ZMod p) *
        (if r ≤ r + j then (-1 : ZMod p) ^ (r + j - r) * ((r + j).choose r : ZMod p) else 0) =
        (n.choose r : ZMod p) * ((-1 : ZMod p) ^ j * ((n-r).choose j : ZMod p)) := by
      rw [if_pos (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
      have h := Nat.choose_mul (n := n) (k := r + j) (s := r) (Nat.le_add_right _ _)
      have hc : (n.choose (r+j) : ZMod p) * ((r+j).choose r : ZMod p) =
          (n.choose r : ZMod p) * ((n-r).choose j : ZMod p) := by
        have h' : n.choose (r+j) * (r+j).choose r = n.choose r * (n-r).choose j := by
          simpa only [Nat.add_sub_cancel_left] using h
        simpa only [Nat.cast_mul] using congrArg (fun z : ℕ => (z : ZMod p)) h'
      calc
        _ = ((n.choose (r+j) : ZMod p) * ((r+j).choose r : ZMod p)) * (-1 : ZMod p)^j := by ring
        _ = _ := by rw [hc]; ring
    simp_rw [hterm]
    rw [← Finset.mul_sum, alternating_choose_sum]
    by_cases heq : n = r
    · subst n
      simp
    · rw [if_neg (by omega), mul_zero, if_neg heq]
  · rw [if_neg (by omega : n ≠ r)]
    apply Finset.sum_eq_zero
    intro j hj
    rw [if_neg (by have := Finset.mem_range.mp hj; omega), mul_zero]

private theorem binomial_inverse_kernel_extended (p q n r : ℕ) (hn : n < q) :
    (∑ j ∈ Finset.range q, (n.choose j : ZMod p) *
      (if r ≤ j then (-1 : ZMod p) ^ (j - r) * (j.choose r : ZMod p) else 0)) =
      if n = r then 1 else 0 := by
  rw [← binomial_inverse_kernel p n r]
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro j hj hjn
  rw [Nat.choose_eq_zero_of_lt (by have := Finset.mem_range.not.mp hjn; omega), Nat.cast_zero, zero_mul]

private theorem binomialMatrix_mulVec_explicitDetectorCoefficient (p q w : ℕ) (hq : 0 < q) :
    (binomialMatrix p q).mulVec (explicitDetectorCoefficient p q w) =
      fun i => if i.val = w % q then 0 else 1 := by
  classical
  funext i
  change (∑ j : Fin q, (i.val.choose j.val : ZMod p) *
    ((if j.val = 0 then 1 else 0) -
      (if w % q ≤ j.val then (-1 : ZMod p)^(j.val-w%q) * (j.val.choose (w%q) : ZMod p) else 0))) = _
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  have hconst : (∑ j : Fin q, (i.val.choose j.val : ZMod p) * (if j.val = 0 then 1 else 0)) = 1 := by
    rw [Finset.sum_eq_single ⟨0, hq⟩]
    · simp
    · intro j hj hj0
      rw [if_neg (by intro h; exact hj0 (Fin.ext h)), mul_zero]
    · simp
  rw [hconst]
  have hkernel := binomial_inverse_kernel_extended p q i.val (w%q) i.isLt
  rw [← Fin.sum_univ_eq_sum_range] at hkernel
  rw [hkernel]
  split_ifs <;> simp_all

private theorem detectorCoefficients_explicit (p q w : ℕ) (hq : 0 < q) :
    detectorCoefficients p q w = explicitDetectorCoefficient p q w := by
  rw [detectorCoefficients, ← binomialMatrix_mulVec_explicitDetectorCoefficient p q w hq,
    Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (by rw [binomialMatrix_det]; exact isUnit_one),
    Matrix.one_mulVec]

end CatalyticTreeEval.Main

open CatalyticTreeEval.Main

theorem solution (p q w : ℕ) (hq : 0 < q) :
    detectorCoefficients p q w = explicitDetectorCoefficient p q w :=
  detectorCoefficients_explicit p q w hq
