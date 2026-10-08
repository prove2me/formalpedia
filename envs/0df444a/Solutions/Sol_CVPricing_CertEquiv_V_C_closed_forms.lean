-- Prove2me | solution 1 for CVPricing.CertEquiv.V_C_closed_forms
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T15:59:44.021521+00:00
-- url     : https://prove2.me/submissions/d5e783c6-b2a1-45a8-86b1-6ebf2a5d8dc2

import Mathlib
import Definitions.Def_CVPricing_CertEquiv_EventA

set_option autoImplicit false

theorem fb361537_split (f : ℕ → ℝ) {n : ℕ} (hn : 2 ≤ n) :
    ∑ s ∈ Finset.Icc 1 n, f s = f 1 + f 2 + ∑ s ∈ Finset.Icc 3 n, f s := by
  induction n, hn using Nat.le_induction with
  | base =>
    rw [show Finset.Icc 3 2 = (∅ : Finset ℕ) from rfl,
      show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) from rfl]
    simp
  | succ m hm ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega), ih]
    ring

theorem fb361537_const (f : ℕ → ℝ) (c : ℝ) {n : ℕ} (hn : 2 ≤ n)
    (hf : ∀ i : ℕ, 3 ≤ i → i ≤ n → f i = c) :
    ∑ s ∈ Finset.Icc 3 n, f s = ((n : ℝ) - 2) * c := by
  rw [Finset.sum_congr rfl (fun i hi => hf i (Finset.mem_Icc.1 hi).1 (Finset.mem_Icc.1 hi).2),
    Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  congr 1
  rw [show n + 1 - 3 = n - 2 by omega, Nat.cast_sub hn]
  norm_num

theorem fb361537_avg (ph : ℝ) (p : ℕ → ℝ) {n : ℕ} (hn : 2 ≤ n)
    (hph : ∀ i : ℕ, 3 ≤ i → i ≤ n → p i = ph) :
    KeskinZeevi.SufficientConditions.avgPriceOf p n = ph - (2 * ph - p 1 - p 2) / n := by
  unfold KeskinZeevi.SufficientConditions.avgPriceOf
  rw [fb361537_split p hn, fb361537_const p ph hn hph]
  have hn' : (n : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  field_simp
  ring

open KeskinZeevi.SufficientConditions in
theorem fb361537_avg2 (e : ℕ → ℝ) : avgPriceOf e 2 = (e 1 + e 2) / 2 := by
  unfold avgPriceOf
  rw [show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) from rfl]
  simp

open KeskinZeevi.SufficientConditions in
theorem solution (ph : ℝ) (p e : ℕ → ℝ) {t : ℕ} (ht : 2 ≤ t)
    (hph : ∀ i : ℕ, 3 ≤ i → i ≤ t → p i = ph) :
    (∀ i : ℕ, 3 ≤ i → i ≤ t → avgPriceOf p i = ph - (2 * ph - p 1 - p 2) / i) ∧
      infoMetricOf p t =
        (1 / 2) * (p 2 - p 1) ^ 2 + (2 * ph - p 1 - p 2) ^ 2 * (1 / 2 - (t : ℝ)⁻¹) ∧
      CVPricing.CertEquiv.crossSum p e t =
        (1 / 2) * (p 2 - p 1) * (e 2 - e 1) +
          (2 * ph - p 1 - p 2) * (avgPriceOf e t - avgPriceOf e 2) := by
  have ht' : (t : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ t := by exact_mod_cast ht
    linarith
  have hA := fb361537_avg ph p ht hph
  refine ⟨?_, ?_, ?_⟩
  · intro i hi hit
    exact fb361537_avg ph p (by omega) (fun j hj hji => hph j hj (by omega))
  · unfold infoMetricOf
    rw [fb361537_split _ ht,
      fb361537_const (fun s => (p s - avgPriceOf p t) ^ 2) ((ph - avgPriceOf p t) ^ 2) ht
        (fun i hi hit => by simp only [hph i hi hit]), hA]
    field_simp
    ring
  · unfold CVPricing.CertEquiv.crossSum
    have hE : ∑ s ∈ Finset.Icc 3 t, e s = t * avgPriceOf e t - e 1 - e 2 := by
      unfold avgPriceOf
      rw [fb361537_split e ht]
      field_simp
      ring
    have hsplit : ∑ s ∈ Finset.Icc 3 t, (p s - avgPriceOf p t) * e s
        = (ph - avgPriceOf p t) * ∑ s ∈ Finset.Icc 3 t, e s := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i hi => by
        rw [hph i (Finset.mem_Icc.1 hi).1 (Finset.mem_Icc.1 hi).2])
    rw [fb361537_split _ ht, hsplit, hE, fb361537_avg2, hA]
    field_simp
    ring
