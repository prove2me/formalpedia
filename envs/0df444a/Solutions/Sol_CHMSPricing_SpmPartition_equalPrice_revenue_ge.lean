-- Prove2me | solution 1 for CHMSPricing.SpmPartition.equalPrice_revenue_ge
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T04:56:49.372685+00:00
-- url     : https://prove2.me/submissions/8b6492b9-9bf9-4e93-a796-2b17c7dffe9f

import Mathlib
import Definitions.Def_CHMSPricing_SpmPartition_Spm

namespace BffdfHelpers

open Finset

/-- telescoping on ℕ-indexed sequences -/
lemma tele_range (g : ℕ → ℝ) (m : ℕ) :
    ∑ k ∈ range m, (∏ j ∈ range k, (1 - g j)) * g k = 1 - ∏ j ∈ range m, (1 - g j) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih, prod_range_succ]
    ring

lemma amgm_one_sub {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) :
    ∏ i, (1 - q i) ≤ (1 - (∑ i, q i) / n) ^ n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have key := Real.geom_mean_le_arith_mean_weighted (Finset.univ : Finset (Fin n))
    (fun _ => (n : ℝ)⁻¹) (fun i => 1 - q i) (fun _ _ => by positivity)
    (by simp [Finset.card_univ]; field_simp)
    (fun i _ => by linarith [(hq i).2])
  have hsum : ∑ i : Fin n, (n : ℝ)⁻¹ * (1 - q i) = 1 - (∑ i, q i) / n := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib]
    simp [Finset.card_univ]
    field_simp
  rw [hsum] at key
  have h0 : 0 ≤ ∏ i : Fin n, (1 - q i) ^ ((n : ℝ)⁻¹) :=
    Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (by linarith [(hq i).2]) _)
  have := pow_le_pow_left₀ h0 key n
  rw [← Finset.prod_pow] at this
  have e : ∀ i : Fin n, ((1 - q i) ^ ((n : ℝ)⁻¹)) ^ n = 1 - q i := fun i =>
    Real.rpow_inv_natCast_pow (by linarith [(hq i).2]) hn.ne'
  simpa [e] using this

lemma exp_bound {n : ℕ} (hn : 0 < n) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (1 - 1 / Real.exp 1) * s ≤ 1 - (1 - s / n) ^ n := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : 0 ≤ 1 - s / n := by
    rw [sub_nonneg, div_le_one (by linarith)]; linarith
  have h2 : (1 - s / n) ^ n ≤ Real.exp (-s) := by
    calc (1 - s / n) ^ n ≤ (Real.exp (-(s / n))) ^ n := by
          apply pow_le_pow_left₀ h1
          have := Real.add_one_le_exp (-(s / n)); linarith
      _ = Real.exp (-s) := by
          rw [← Real.exp_nat_mul]; congr 1; field_simp
  have h3 : Real.exp (-s) ≤ (1 - s) * Real.exp 0 + s * Real.exp (-1) := by
    have := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (-1 : ℝ))
      (by linarith : 0 ≤ 1 - s) hs0 (by ring)
    simpa [smul_eq_mul] using this
  rw [Real.exp_zero, Real.exp_neg 1] at h3
  rw [one_div]
  nlinarith

end BffdfHelpers

open BffdfHelpers in
open CHMSPricing.SpmPartition in
theorem solution {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (hs : ∑ i, q i ≤ 1) (pbar : ℝ) (hpbar : 0 ≤ pbar) :
    pbar * ∑ i, oneUnitOfferProb q i * q i = pbar * (1 - ∏ i, (1 - q i)) ∧
    pbar * (1 - (1 - (∑ i, q i) / n) ^ n) ≤ pbar * (1 - ∏ i, (1 - q i)) ∧
    (1 - 1 / Real.exp 1) * pbar * (∑ i, q i) ≤ pbar * (1 - (1 - (∑ i, q i) / n) ^ n) := by
  refine ⟨?_, ?_, ?_⟩
  · congr 1
    set g : ℕ → ℝ := fun j => if h : j < n then q ⟨j, h⟩ else 0 with hg
    have hgq : ∀ i : Fin n, g i = q i := fun i => by simp [hg, i.isLt]
    have hc : ∀ k : Fin n, oneUnitOfferProb q k = ∏ j ∈ Finset.range k, (1 - g j) := by
      intro k
      unfold oneUnitOfferProb
      rw [Finset.prod_filter]
      trans ∏ a : Fin n, (fun j : ℕ => if j < (k : ℕ) then 1 - g j else 1) (a : ℕ)
      · apply Finset.prod_congr rfl
        intro a _
        show _ = (if (a : ℕ) < (k : ℕ) then 1 - g a else 1)
        rw [hgq]; exact if_congr Fin.lt_def.symm rfl rfl
      rw [Fin.prod_univ_eq_prod_range (fun j : ℕ => if j < (k : ℕ) then 1 - g j else 1) n]
      rw [← Finset.prod_filter]
      congr 1
      ext j; simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨_, h⟩; exact h
      · intro h; exact ⟨lt_trans h k.isLt, h⟩
    have lhs : ∑ i : Fin n, oneUnitOfferProb q i * q i
        = ∑ k ∈ Finset.range n, (∏ j ∈ Finset.range k, (1 - g j)) * g k := by
      rw [← Fin.sum_univ_eq_sum_range (fun k => (∏ j ∈ Finset.range k, (1 - g j)) * g k) n]
      simp [hc, hgq]
    have rhs : ∏ i : Fin n, (1 - q i) = ∏ j ∈ Finset.range n, (1 - g j) := by
      rw [← Fin.prod_univ_eq_prod_range (fun j => 1 - g j) n]
      simp [hgq]
    rw [lhs, rhs, tele_range]
  · apply mul_le_mul_of_nonneg_left _ hpbar
    linarith [amgm_one_sub hn q hq]
  · have hs0 : 0 ≤ ∑ i, q i := Finset.sum_nonneg (fun i _ => (hq i).1)
    have := mul_le_mul_of_nonneg_left (exp_bound hn _ hs0 hs) hpbar
    linarith
