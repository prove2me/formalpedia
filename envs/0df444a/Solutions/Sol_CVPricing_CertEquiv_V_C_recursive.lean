-- Prove2me | solution 1 for CVPricing.CertEquiv.V_C_recursive
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T15:34:13.20249+00:00
-- url     : https://prove2.me/submissions/19702bbb-c2b7-4673-bb7a-8eec31de98dc

import Mathlib
import Definitions.Def_CVPricing_CertEquiv_EventA

open KeskinZeevi.SufficientConditions in
lemma vcr49_cross_closed (p e : ℕ → ℝ) (t : ℕ) :
    ∑ i ∈ Finset.Icc 1 t, (p i - avgPriceOf p t) * e i =
      ∑ i ∈ Finset.Icc 1 t, p i * e i
        - (∑ i ∈ Finset.Icc 1 t, p i) * (∑ i ∈ Finset.Icc 1 t, e i) / t := by
  unfold avgPriceOf
  simp only [sub_mul, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum]
  ring

open KeskinZeevi.SufficientConditions in
lemma vcr49_sq_eq_cross (p : ℕ → ℝ) (t : ℕ) :
    ∑ i ∈ Finset.Icc 1 t, (p i - avgPriceOf p t) ^ 2 =
      ∑ i ∈ Finset.Icc 1 t, (p i - avgPriceOf p t) * p i := by
  have h0 : ∑ i ∈ Finset.Icc 1 t, (p i - avgPriceOf p t) * avgPriceOf p t = 0 := by
    rw [← Finset.sum_mul, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    unfold avgPriceOf
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp
    · have : (t : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
      field_simp
      ring
  have : ∀ i, (p i - avgPriceOf p t) ^ 2 =
      (p i - avgPriceOf p t) * p i - (p i - avgPriceOf p t) * avgPriceOf p t := fun i => by ring
  simp only [this, Finset.sum_sub_distrib, h0, sub_zero]

open KeskinZeevi.SufficientConditions in
lemma vcr49_main (p e : ℕ → ℝ) (t : ℕ) :
    ∑ i ∈ Finset.Icc 1 t, (p i - avgPriceOf p t) * e i =
      ∑ i ∈ Finset.Icc 2 t,
          ((i : ℝ) - 1) / i * (p i - avgPriceOf p (i - 1)) * (e i - avgPriceOf e (i - 1)) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp [avgPriceOf]
    rw [vcr49_cross_closed] at ih ⊢
    rw [Finset.sum_Icc_succ_top (show 2 ≤ t + 1 by omega), ← ih]
    simp only [Finset.sum_Icc_succ_top (show 1 ≤ t + 1 by omega)]
    simp only [Nat.add_sub_cancel]
    unfold avgPriceOf
    have htr : (t : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
    have ht1 : ((t : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

open KeskinZeevi.SufficientConditions CVPricing.CertEquiv in
theorem solution (p e : ℕ → ℝ) {t : ℕ} (ht : 2 ≤ t) :
    infoMetricOf p t =
        ∑ i ∈ Finset.Icc 2 t, ((i : ℝ) - 1) / i * (p i - avgPriceOf p (i - 1)) ^ 2 ∧
      crossSum p e t =
        ∑ i ∈ Finset.Icc 2 t,
          ((i : ℝ) - 1) / i * (p i - avgPriceOf p (i - 1)) * (e i - avgPriceOf e (i - 1)) := by
  refine ⟨?_, ?_⟩
  · unfold infoMetricOf
    rw [vcr49_sq_eq_cross, vcr49_main]
    refine Finset.sum_congr rfl fun i _ => by ring
  · unfold crossSum
    exact vcr49_main p e t
