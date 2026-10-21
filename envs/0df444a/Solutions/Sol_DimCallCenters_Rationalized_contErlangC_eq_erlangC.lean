-- Prove2me | solution 1 for DimCallCenters.Rationalized.contErlangC_eq_erlangC
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T22:06:06.145213+00:00
-- url     : https://prove2.me/submissions/d3dae6c5-4d21-479a-9996-88b008bb9d90

import Mathlib
import Definitions.Def_DimCallCenters_Rationalized_erlangC
import Definitions.Def_DimCallCenters_Rationalized_contErlangC

set_option autoImplicit false
open DimCallCenters.Rationalized MeasureTheory Set

lemma dcc_gam_int (α : ℝ) (hα : 0 < α) (k : ℕ) :
    ∫ t in Ioi (0:ℝ), t ^ k * Real.exp (-(α * t)) = (k.factorial : ℝ) / α ^ (k + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (k:ℝ) + 1) (r := α) (by positivity) hα
  have e : ((k:ℝ) + 1) - 1 = (k:ℝ) := by ring
  have e2 : ((k:ℝ) + 1) = ((k + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [e] at h
  simp only [Real.rpow_natCast] at h
  have hg : Real.Gamma ((k + 1 : ℕ) : ℝ) = (k.factorial : ℝ) := by
    rw [Nat.cast_succ]; exact Real.Gamma_nat_eq_factorial k
  rw [e2, Real.rpow_natCast, hg] at h
  rw [h, one_div, inv_pow]
  field_simp

lemma dcc_gam_intble (α : ℝ) (hα : 0 < α) (k : ℕ) :
    IntegrableOn (fun t : ℝ => t ^ k * Real.exp (-(α * t))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (k:ℝ)) (b := α)
    (by have : (0:ℝ) ≤ k := Nat.cast_nonneg k; linarith) one_pos hα
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_natCast, Real.rpow_one, neg_mul]

lemma dcc_alpha_I (α : ℝ) (hα : 0 < α) (n : ℕ) :
    α * ∫ t in Ioi (0:ℝ), Real.exp (-α * t) * t * (1 + t) ^ ((n:ℝ) + 1 - 1) =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * ((k + 1).factorial : ℝ) / α ^ (k + 1) := by
  have e : ((n:ℝ) + 1 - 1) = (n:ℝ) := by ring
  simp only [e, Real.rpow_natCast]
  have hpt : ∀ t : ℝ, Real.exp (-α * t) * t * (1 + t) ^ n =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * (t ^ (k + 1) * Real.exp (-(α * t))) := by
    intro t
    rw [add_comm 1 t, add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [neg_mul]; simp only [one_pow, mul_one]; ring
  simp_rw [hpt]
  rw [integral_finset_sum _ (fun k _ => ((dcc_gam_intble α hα (k + 1)).const_mul _))]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [integral_const_mul, dcc_gam_int α hα (k + 1)]
  have : α ^ (k + 1 + 1) = α ^ (k+1) * α := pow_succ _ _
  rw [this]
  have hne : α ^ (k+1) ≠ 0 := by positivity
  field_simp

lemma dcc_refl (α : ℝ) (hα : 0 < α) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * ((k + 1).factorial : ℝ) / α ^ (k + 1) =
      (n.factorial : ℝ) / α ^ (n + 1) *
        ∑ j ∈ Finset.range (n + 1), ((n + 1 : ℝ) - j) * α ^ j / (j.factorial : ℝ) := by
  rw [← Finset.sum_range_reflect, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hj' : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [show n + 1 - 1 - j = n - j by omega, Nat.choose_symm hj', Nat.cast_choose ℝ hj',
    Nat.factorial_succ, Nat.cast_mul]
  push_cast [Nat.cast_sub hj']
  have h1 : α ^ (n - j + 1) * α ^ j = α ^ (n + 1) := by rw [← pow_add]; congr 1; omega
  have hne1 : (j.factorial : ℝ) ≠ 0 := by positivity
  have hne2 : ((n - j).factorial : ℝ) ≠ 0 := by positivity
  have hne3 : α ^ (n - j + 1) ≠ 0 := by positivity
  have hne4 : α ^ j ≠ 0 := by positivity
  have hne5 : α ^ (n + 1) ≠ 0 := by positivity
  rw [← h1]
  push_cast
  field_simp
  ring

lemma dcc_A (α : ℝ) (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), ((n + 1 : ℝ) - j) * α ^ j / (j.factorial : ℝ) =
      ((n + 1 : ℝ) - α) * ∑ j ∈ Finset.range (n + 1), α ^ j / (j.factorial : ℝ)
        + α ^ (n + 1) / (n.factorial : ℝ) := by
  induction n with
  | zero => simp
  | succ m ih =>
    have h1 : ∑ j ∈ Finset.range (m + 1 + 1), ((((m + 1 : ℕ) : ℝ) + 1) - j) * α ^ j / (j.factorial : ℝ)
        = ∑ j ∈ Finset.range (m + 1), (((m : ℝ) + 1) - j) * α ^ j / (j.factorial : ℝ)
          + ∑ j ∈ Finset.range (m + 1 + 1), α ^ j / (j.factorial : ℝ) := by
      rw [Finset.sum_range_succ _ (m + 1), Finset.sum_range_succ (fun j : ℕ => α ^ j / (j.factorial : ℝ)) (m + 1),
        ← add_assoc, ← Finset.sum_add_distrib]
      have : ∀ x ∈ Finset.range (m + 1), ((((m + 1 : ℕ) : ℝ) + 1) - x) * α ^ x / (x.factorial : ℝ)
          = (((m : ℝ) + 1) - x) * α ^ x / (x.factorial : ℝ) + α ^ x / (x.factorial : ℝ) := by
        intro x _; push_cast; ring
      rw [Finset.sum_congr rfl this]
      congr 1
      push_cast
      ring
    rw [h1, ih, Finset.sum_range_succ (fun j : ℕ => α ^ j / (j.factorial : ℝ)) (m + 1),
      Nat.factorial_succ]
    have hf : (m.factorial : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

theorem solution (N : ℕ) (ν : ℝ) (hν : 0 < ν) (hνN : ν < N) :
    contErlangC N ν = erlangC N ν := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp at hνN; linarith
    · exact ⟨N - 1, by omega⟩
  have key := dcc_alpha_I ν hν n
  rw [dcc_refl ν hν n, dcc_A ν n] at key
  unfold contErlangC erlangC
  simp only [Nat.cast_add, Nat.cast_one] at hνN ⊢
  rw [key]
  have hS : 0 < ∑ j ∈ Finset.range (n + 1), ν ^ j / (j.factorial : ℝ) :=
    Finset.sum_pos (fun j _ => by positivity) ⟨0, by simp⟩
  set S := ∑ j ∈ Finset.range (n + 1), ν ^ j / (j.factorial : ℝ) with hSdef
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  have hn1 : (0:ℝ) < (n:ℝ) + 1 := by positivity
  have hX : (0:ℝ) < ((n:ℝ) + 1 - ν) * S + ν ^ (n + 1) / (n.factorial : ℝ) := by
    have : 0 < ((n:ℝ) + 1 - ν) * S := mul_pos (by linarith) hS
    positivity
  have hY : (0:ℝ) < (1 - ν / ((n:ℝ) + 1)) * S + ν ^ (n + 1) / (((n + 1).factorial : ℕ) : ℝ) := by
    have : 0 < (1 - ν / ((n:ℝ) + 1)) * S := mul_pos (by rw [sub_pos, div_lt_one hn1]; exact hνN) hS
    positivity
  rw [Nat.factorial_succ] at hY ⊢
  push_cast at hY ⊢
  have hX' := hX.ne'
  have hY' := hY.ne'
  field_simp
