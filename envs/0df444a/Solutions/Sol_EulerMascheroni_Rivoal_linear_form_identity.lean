-- Prove2me | solution 1 for EulerMascheroni.Rivoal.linear_form_identity
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-25T21:32:08.197748+00:00
-- url     : https://prove2.me/submissions/8505a2a1-282e-4596-ac2d-cfc663413174

import Definitions.Def_eulerMascheroni_rivoalForms
import Definitions.Def_eulerMascheroni_mixedCover
import Theorems.Thm_EulerMascheroni_Rivoal_hasSum_alternating_descFactorial
import Theorems.Thm_EulerMascheroni_Rivoal_hasSum_alternating_descFactorial_div_sub
import Theorems.Thm_EulerMascheroni_Rivoal_hasSum_remainder_reindex
import Theorems.Thm_EulerMascheroni_Rivoal_bInt_cast
import Theorems.Thm_EulerMascheroni_Rivoal_partialFraction_value
import Theorems.Thm_EulerMascheroni_Rivoal_polyP_value_at_node
import Theorems.Thm_EulerMascheroni_Rivoal_polyP_newton

open Finset EulerMascheroni.Rivoal

namespace RivoalLFAux

lemma evalN (n M : ℕ) :
    (((polyN n).eval (M : ℤ) : ℤ) : ℂ) = ∏ i ∈ Ico (n + 1) (3 * n + 1), ((M : ℂ) - i) := by
  unfold polyN
  rw [Polynomial.eval_prod, Int.cast_prod]
  have : Icc (n + 1) (3 * n) = Ico (n + 1) (3 * n + 1) := by ext; simp only [mem_Icc, mem_Ico]; omega
  rw [this]
  refine prod_congr rfl (fun i _ => ?_)
  simp

lemma evalD (n M : ℕ) :
    (((polyD n).eval (M : ℤ) : ℤ) : ℂ) = ∏ i ∈ range (n + 1), ((M : ℂ) - i) := by
  unfold polyD
  rw [Polynomial.eval_prod, Int.cast_prod]
  refine prod_congr rfl (fun i _ => ?_)
  simp

lemma bC (n j : ℕ) (hj : j ≤ n) :
    ((bInt n j : ℤ) : ℂ) = (-1) ^ (n - j) * ((beta n j : ℚ) : ℂ) := by
  have h := congrArg (fun q : ℚ => (q : ℂ)) (bInt_cast n j hj)
  push_cast at h
  exact h

lemma sgn (n M : ℕ) (hM : M ≤ n) :
    (-1 : ℂ) ^ (n + 1) * ((-1) ^ M * (-1) ^ (n - M)) = -1 := by
  rw [← pow_add, Nat.add_sub_cancel' hM, ← pow_add, show n + 1 + n = 2 * n + 1 by omega,
    pow_succ, pow_mul]
  norm_num

end RivoalLFAux

open RivoalLFAux in
theorem solution (n : ℕ) (hn : 1 ≤ n) :
    ((EulerMascheroni.Rivoal.pCoef n : ℚ) : ℂ)
      + ((EulerMascheroni.Rivoal.qCoef n : ℚ) : ℂ) * Complex.exp 1
      + ((EulerMascheroni.Rivoal.rCoef n : ℚ) : ℂ) * EulerMascheroni.Mixed.expEin 1
      = Complex.exp 1 * ((EulerMascheroni.Rivoal.remainder n : ℝ) : ℂ) := by
  set E1 : ℂ := Complex.exp (-1) with hE1
  set PC : ℕ → ℂ := fun M => (((polyP n).eval (M : ℤ) : ℤ) : ℂ) with hPC
  set bb : ℕ → ℂ := fun j => ((bInt n j : ℤ) : ℂ) with hbb
  set hC : ℕ → ℂ := fun j => ((hcoef n j : ℚ) : ℂ) with hhC
  set ein1 := EulerMascheroni.Mixed.ein 1 with hein1
  -- Step 1 (complexified)
  have hR : HasSum (fun M : ℕ => if n + 1 ≤ M then
      (-1 : ℂ) ^ M * ((∏ i ∈ Ico (n + 1) (3 * n + 1), ((M : ℂ) - i)) /
        (∏ i ∈ range (n + 1), ((M : ℂ) - i))) / (M.factorial : ℂ) else 0)
      ((-1) ^ (n + 1) * ((remainder n : ℝ) : ℂ)) := by
    have h := Complex.hasSum_ofReal.mpr (hasSum_remainder_reindex n)
    push_cast at h
    refine h.congr_fun (fun M => ?_)
    split_ifs <;> push_cast <;> rfl
  -- Step 3a: polynomial part
  obtain ⟨a, -, hval, hT⟩ := polyP_newton n hn
  have hA : HasSum (fun M : ℕ => (-1 : ℂ) ^ M * PC M / (M.factorial : ℂ))
      (E1 * ((-1) ^ (n + 1) * ((pCoef n : ℚ) : ℂ))) := by
    have hS1 : ∀ j ∈ range n, HasSum (fun M : ℕ => (a j : ℂ) *
        ((-1 : ℂ) ^ M * (M.descFactorial j : ℂ) / (M.factorial : ℂ))) ((a j : ℂ) * ((-1) ^ j * E1)) := by
      intro j _
      have h := Complex.hasSum_ofReal.mpr (hasSum_alternating_descFactorial j)
      push_cast at h
      exact h.mul_left _
    have h := hasSum_sum hS1
    have hT' := congrArg (fun q : ℚ => (q : ℂ)) hT
    push_cast at hT'
    convert h using 1
    · funext M
      have hv := congrArg (fun q : ℚ => (q : ℂ)) (hval M)
      push_cast at hv
      simp only [hPC]
      rw [hv, mul_sum, sum_div]
      refine sum_congr rfl (fun j _ => ?_)
      ring
    · rw [← hT', mul_sum]
      refine sum_congr rfl (fun j _ => ?_)
      ring
  -- Step 3b: simple fractions
  have hB : HasSum (fun M : ℕ => ∑ j ∈ range (n + 1), bb j * (if j < M then
        (-1 : ℂ) ^ M * (M.descFactorial j : ℂ) / ((M.factorial : ℂ) * ((M - j : ℕ) : ℂ)) else 0))
      (∑ j ∈ range (n + 1), bb j * (-(-1) ^ j * ein1)) :=
    hasSum_sum (fun j _ => (hasSum_alternating_descFactorial_div_sub j).mul_left _)
  -- finite correction at the poles
  have hH : HasSum (fun M : ℕ => if M ≤ n then -((-1 : ℂ) ^ M * bb M * hC M) else 0)
      (∑ M ∈ range (n + 1), -((-1 : ℂ) ^ M * bb M * hC M)) := by
    have h : HasSum (fun M : ℕ => if M ≤ n then -((-1 : ℂ) ^ M * bb M * hC M) else 0)
        (∑ M ∈ range (n + 1), if M ≤ n then -((-1 : ℂ) ^ M * bb M * hC M) else 0) :=
      hasSum_sum_of_ne_finset_zero (fun M hM => by
        rw [mem_range, not_lt] at hM
        rw [if_neg (by omega)])
    convert h using 1
    refine sum_congr rfl (fun M hM => ?_)
    rw [if_pos (by have := mem_range.mp hM; omega)]
  -- pointwise identity
  have hpt : ∀ M : ℕ, (-1 : ℂ) ^ M * PC M / (M.factorial : ℂ) +
      (∑ j ∈ range (n + 1), bb j * (if j < M then
        (-1 : ℂ) ^ M * (M.descFactorial j : ℂ) / ((M.factorial : ℂ) * ((M - j : ℕ) : ℂ)) else 0)) -
      (if M ≤ n then -((-1 : ℂ) ^ M * bb M * hC M) else 0) =
      (if n + 1 ≤ M then
      (-1 : ℂ) ^ M * ((∏ i ∈ Ico (n + 1) (3 * n + 1), ((M : ℂ) - i)) /
        (∏ i ∈ range (n + 1), ((M : ℂ) - i))) / (M.factorial : ℂ) else 0) := by
    intro M
    have hMf : (M.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos M).ne'
    by_cases hM : n + 1 ≤ M
    · rw [if_pos hM, if_neg (by omega)]
      have h3 := congrArg (fun q : ℚ => (q : ℂ)) (partialFraction_value n M (by omega))
      push_cast at h3
      rw [evalN, evalD] at h3
      rw [h3]
      have hs : ∀ j ∈ range (n + 1), bb j * (if j < M then
          (-1 : ℂ) ^ M * (M.descFactorial j : ℂ) / ((M.factorial : ℂ) * ((M - j : ℕ) : ℂ)) else 0)
          = (-1 : ℂ) ^ M * ((bb j * (M.descFactorial j : ℂ) / ((M : ℂ) - j))) / (M.factorial : ℂ) := by
        intro j hj
        have hj' := mem_range.mp hj
        rw [if_pos (by omega), Nat.cast_sub (by omega), ← div_div]
        ring
      rw [sum_congr rfl hs, ← sum_div, ← mul_sum, sub_zero]
      simp only [hPC, hbb]
      ring
    · rw [if_neg hM, if_pos (by omega)]
      have h4 := congrArg (fun q : ℚ => (q : ℂ)) (polyP_value_at_node n M (by omega))
      push_cast at h4
      have hsplit := sum_range_add_sum_Ico (fun j => bb j * (if j < M then
          (-1 : ℂ) ^ M * (M.descFactorial j : ℂ) / ((M.factorial : ℂ) * ((M - j : ℕ) : ℂ)) else 0))
          (show M ≤ n + 1 by omega)
      rw [← hsplit]
      have hz : ∑ j ∈ Ico M (n + 1), bb j * (if j < M then
          (-1 : ℂ) ^ M * (M.descFactorial j : ℂ) / ((M.factorial : ℂ) * ((M - j : ℕ) : ℂ)) else 0) = 0 := by
        refine sum_eq_zero (fun j hj => ?_)
        rw [if_neg (by have := (mem_Ico.mp hj).1; omega), mul_zero]
      have hs : ∀ j ∈ range M, bb j * (if j < M then
          (-1 : ℂ) ^ M * (M.descFactorial j : ℂ) / ((M.factorial : ℂ) * ((M - j : ℕ) : ℂ)) else 0)
          = (-1 : ℂ) ^ M * ((bb j * (M.descFactorial j : ℂ) / ((M : ℂ) - j))) / (M.factorial : ℂ) := by
        intro j hj
        have hj' := mem_range.mp hj
        rw [if_pos hj', Nat.cast_sub (by omega), ← div_div]
        ring
      rw [hz, add_zero, sum_congr rfl hs, ← sum_div, ← mul_sum]
      have key : (-1 : ℂ) ^ M * PC M / (M.factorial : ℂ) +
          (-1 : ℂ) ^ M * (∑ j ∈ range M, bb j * (M.descFactorial j : ℂ) / ((M : ℂ) - j)) /
            (M.factorial : ℂ)
          = (-1 : ℂ) ^ M / (M.factorial : ℂ) * (PC M +
              ∑ j ∈ range M, bb j * (M.descFactorial j : ℂ) / ((M : ℂ) - j)) := by ring
      rw [key]
      simp only [hPC, hbb, hhC]
      rw [h4]
      field_simp
      ring
  -- combine
  have htot := ((hA.add hB).sub hH).congr_fun (fun M => (hpt M).symm)
  have heq := htot.unique hR
  -- final algebra
  set s : ℂ := (-1) ^ (n + 1) with hs
  set SR : ℂ := ∑ j ∈ range (n + 1), bb j * (-(-1) ^ j) with hSR
  set SQ : ℂ := ∑ M ∈ range (n + 1), (-1 : ℂ) ^ M * bb M * hC M with hSQ
  have hSB : ∑ j ∈ range (n + 1), bb j * (-(-1) ^ j * ein1) = ein1 * SR := by
    rw [hSR, mul_sum]; refine sum_congr rfl (fun j _ => ?_); ring
  have hSH : ∑ M ∈ range (n + 1), -((-1 : ℂ) ^ M * bb M * hC M) = -SQ := by
    rw [hSQ, sum_neg_distrib]
  rw [hSB, hSH] at heq
  have hq : s * SQ = ((qCoef n : ℚ) : ℂ) := by
    rw [hSQ, mul_sum]
    simp only [qCoef]
    push_cast
    rw [← sum_neg_distrib]
    refine sum_congr rfl (fun M hM => ?_)
    have hM' : M ≤ n := by have := mem_range.mp hM; omega
    simp only [hbb, hhC]
    rw [bC n M hM']
    have := sgn n M hM'
    linear_combination (((beta n M : ℚ) : ℂ) * ((hcoef n M : ℚ) : ℂ)) * this
  have hr : s * SR = ((rCoef n : ℚ) : ℂ) := by
    rw [hSR, mul_sum]
    simp only [rCoef]
    push_cast
    refine sum_congr rfl (fun j hj => ?_)
    have hj' : j ≤ n := by have := mem_range.mp hj; omega
    simp only [hbb]
    rw [bC n j hj']
    have := sgn n j hj'
    linear_combination (-((beta n j : ℚ) : ℂ)) * this
  have hsq : s ^ 2 = 1 := by rw [hs, ← pow_mul, mul_comm, pow_mul]; norm_num
  have hE : Complex.exp 1 * E1 = 1 := by
    rw [hE1, ← Complex.exp_add]; norm_num
  have hexpEin : EulerMascheroni.Mixed.expEin 1 = Complex.exp 1 * ein1 := rfl
  rw [hexpEin]
  set e := Complex.exp 1
  set rem : ℂ := ((remainder n : ℝ) : ℂ)
  set pC : ℂ := ((pCoef n : ℚ) : ℂ)
  -- heq : E1 * (s * pC) + ein1 * SR - -SQ = s * rem
  linear_combination (e * s) * heq - pC * hE - pC * e * E1 * hsq - e * hq - e * ein1 * hr + e * rem * hsq
