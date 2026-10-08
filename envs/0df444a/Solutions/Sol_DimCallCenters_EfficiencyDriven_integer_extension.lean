-- Prove2me | solution 1 for DimCallCenters.EfficiencyDriven.integer_extension
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T14:21:16.97185+00:00
-- url     : https://prove2.me/submissions/fab51748-5f12-48b7-91fd-6c481ed87bb9

import Mathlib
import Definitions.Def_DimCallCenters_Rationalized_erlangC
import Definitions.Def_DimCallCenters_Rationalized_contErlangC

namespace P55614631

open MeasureTheory Set

lemma intOn_pow (k : ℕ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => t ^ k * Real.exp (-a * t)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (k : ℝ)) (p := 1) (b := a)
    (by have : (0:ℝ) ≤ k := Nat.cast_nonneg k; linarith) one_pos ha
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp [Real.rpow_natCast, Real.rpow_one]

lemma int_pow (k : ℕ) {a : ℝ} (ha : 0 < a) :
    ∫ t in Ioi (0:ℝ), t ^ k * Real.exp (-a * t) = (k.factorial : ℝ) / a ^ (k + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (k : ℝ) + 1) (r := a)
    (by positivity) ha
  have h2 : ∫ t in Ioi (0:ℝ), t ^ k * Real.exp (-a * t)
      = ∫ t in Ioi (0:ℝ), t ^ ((k : ℝ) + 1 - 1) * Real.exp (-(a * t)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    simp [Real.rpow_natCast, neg_mul]
  rw [h2, h]
  have hG : Real.Gamma ((k : ℝ) + 1) = (k.factorial : ℝ) := Real.Gamma_nat_eq_factorial k
  rw [hG]
  have : (1 / a) ^ ((k : ℝ) + 1) = 1 / a ^ (k + 1) := by
    rw [show ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    rw [one_div_pow]
  rw [this]; ring

lemma integrand_eq (m : ℕ) (a t : ℝ) :
    Real.exp (-a * t) * (1 + t) ^ m
      = ∑ k ∈ Finset.range (m + 1), (m.choose k : ℝ) * (t ^ k * Real.exp (-a * t)) := by
  rw [add_comm (1:ℝ) t, add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [one_pow]; ring

lemma intOn_A (m : ℕ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => Real.exp (-a * t) * (1 + t) ^ m) (Ioi 0) := by
  simp_rw [integrand_eq m a]
  exact integrable_finsetSum _ (fun k _ => (intOn_pow k ha).const_mul _)

lemma sum_eq (m : ℕ) {a : ℝ} (ha : 0 < a) :
    ∑ k ∈ Finset.range (m + 1), (m.choose k : ℝ) * ((k.factorial : ℝ) / a ^ (k + 1))
      = (m.factorial : ℝ) / a ^ (m + 1) *
          ∑ j ∈ Finset.range (m + 1), a ^ j / (j.factorial : ℝ) := by
  rw [Finset.mul_sum, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hk' : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hsub : m + 1 - 1 - k = m - k := by omega
  rw [hsub]
  have hfac : ((m.choose k : ℕ) : ℝ) * (k.factorial : ℝ) * ((m - k).factorial : ℝ)
      = (m.factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk'
  have hpow : a ^ (m + 1) = a ^ (k + 1) * a ^ (m - k) := by
    rw [← pow_add]; congr 1; omega
  rw [← hfac, hpow]
  have h1 : (0:ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have h2 : (0:ℝ) < ((m - k).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  field_simp
  rw [Nat.choose_symm hk']
  ring

lemma int_A (m : ℕ) {a : ℝ} (ha : 0 < a) :
    ∫ t in Ioi (0:ℝ), Real.exp (-a * t) * (1 + t) ^ m
      = (m.factorial : ℝ) / a ^ (m + 1) *
          ∑ j ∈ Finset.range (m + 1), a ^ j / (j.factorial : ℝ) := by
  simp_rw [integrand_eq m a]
  rw [integral_finsetSum _ (fun k _ => (intOn_pow k ha).const_mul _)]
  simp_rw [integral_const_mul, int_pow _ ha]
  exact sum_eq m ha

end P55614631

open MeasureTheory Set in
theorem solution (ν : ℝ) (N : ℕ) (hν : 0 < ν)
    (hstable : ν < (N : ℝ)) :
    DimCallCenters.Rationalized.contErlangC N ν = DimCallCenters.Rationalized.erlangC N ν := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := by
    rcases N with _ | n
    · simp at hstable; linarith
    · exact ⟨n, rfl⟩
  unfold DimCallCenters.Rationalized.contErlangC DimCallCenters.Rationalized.erlangC
  set a := ν with ha_def
  have ha : 0 < a := hν
  have hint : ∫ t in Ioi (0:ℝ), Real.exp (-a * t) * t * (1 + t) ^ (((n + 1 : ℕ) : ℝ) - 1)
      = ∫ t in Ioi (0:ℝ), (Real.exp (-a * t) * (1 + t) ^ (n + 1)
          - Real.exp (-a * t) * (1 + t) ^ n) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    rw [show (((n + 1 : ℕ) : ℝ) - 1) = (n : ℝ) by push_cast; ring, Real.rpow_natCast]
    ring
  rw [hint, integral_sub (P55614631.intOn_A _ ha) (P55614631.intOn_A _ ha),
    P55614631.int_A _ ha, P55614631.int_A _ ha]
  rw [Finset.sum_range_succ (fun j => a ^ j / (j.factorial : ℝ)) (n + 1)]
  set S := ∑ j ∈ Finset.range (n + 1), a ^ j / (j.factorial : ℝ)
  rw [Nat.factorial_succ]
  push_cast
  have hf : (0:ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  rw [← inv_inv (a ^ (n + 1) / (((n:ℝ) + 1) * (n.factorial : ℝ))), ← mul_inv]
  congr 1
  field_simp
  ring
