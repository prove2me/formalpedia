-- Prove2me | solution 1 for Erdos287.local_sieve_density_with_repeated_roots
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T20:04:08.503982+00:00
-- url     : https://prove2.me/submissions/156d65c6-1f11-475e-94e1-9b424736aa35

import Mathlib

open Finset

set_option autoImplicit false

/-- Local weighted counts group auxiliary coordinates by their zero residue.
The density for one more coordinate depends on whether it adds a new root. -/
theorem solution {ι ρ : Type*} [DecidableEq ι] [DecidableEq ρ]
    (T : Finset ι) (R : Finset ρ) (root : ι → ρ) (j : ρ)
    (w : ι → ℂ) (ε : ℝ) (hε : ε ≤ 1)
    (hw : ∀ i ∈ T, ‖w i‖ ≤ ε)
    (hroot : T.image root ⊆ R) (hproper : (T.image root).card < R.card) :
    let H := T.image root
    let Q := R \ H
    let K := ∑ x ∈ R, ∏ i ∈ T.filter (fun i => root i = x), w i
    let g : ℝ := if j ∈ Q then 1 / (Q.card : ℝ) else 0
    ‖K - (Q.card : ℂ)‖ ≤ (H.card : ℝ) * ε ∧
      (Q.card : ℝ) * (1 - g) = ((Q.erase j).card : ℝ) ∧
      (j ∈ Q → ‖1 - K / (Q.card : ℂ)‖ ≤ (H.card : ℝ) * ε / Q.card) := by
  intro H Q K g
  let W (x : ρ) := ∏ i ∈ T.filter (fun i => root i = x), w i
  have hcard : 0 < Q.card := by
    change 0 < (R \ T.image root).card
    rw [card_sdiff_of_subset hroot]
    omega
  have hnorm (x : ρ) (hx : x ∈ H) : ‖W x‖ ≤ ε := by
    obtain ⟨i, hi, hir⟩ := mem_image.mp hx
    let U := T.filter (fun k => root k = x)
    have hiU : i ∈ U := mem_filter.mpr ⟨hi, hir⟩
    have hrest : ‖∏ k ∈ U.erase i, w k‖ ≤ 1 := by
      rw [Complex.norm_prod]
      exact Finset.prod_le_one (fun k _ => norm_nonneg (w k)) (fun k hk =>
        (hw k (mem_filter.mp (mem_of_mem_erase hk)).1).trans hε)
    change ‖∏ k ∈ U, w k‖ ≤ ε
    rw [← prod_erase_mul U w hiU, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg (w i)) hrest).trans (hw i hi)
  have hneutral (x : ρ) (hx : x ∈ Q) : W x = 1 := by
    have hne : x ∉ H := (mem_sdiff.mp hx).2
    have hfilter : T.filter (fun i => root i = x) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro i hi
      obtain ⟨hi, he⟩ := mem_filter.mp hi
      exact hne (mem_image.mpr ⟨i, hi, he⟩)
    simp [W, hfilter]
  have hsum : K = (Q.card : ℂ) + ∑ x ∈ H, W x := by
    change (∑ x ∈ R, W x) = _
    rw [← sum_sdiff hroot]
    congr 1
    calc
      ∑ x ∈ Q, W x = ∑ _x ∈ Q, (1 : ℂ) := sum_congr rfl hneutral
      _ = _ := by simp
  have herror : ‖K - (Q.card : ℂ)‖ ≤ (H.card : ℝ) * ε := by
    rw [hsum, add_sub_cancel_left]
    calc
      ‖∑ x ∈ H, W x‖ ≤ ∑ x ∈ H, ‖W x‖ := norm_sum_le _ _
      _ ≤ ∑ _x ∈ H, ε := sum_le_sum hnorm
      _ = _ := by simp [nsmul_eq_mul]
  refine ⟨herror, ?_, ?_⟩
  · by_cases hj : j ∈ Q
    · have hQ : (Q.card : ℝ) ≠ 0 := by exact_mod_cast hcard.ne'
      simp only [g, hj, if_true, card_erase_of_mem hj,
        Nat.cast_sub (Nat.succ_le_of_lt hcard), Nat.cast_one]
      field_simp
    · simp [g, hj]
  · intro _hj
    have hQ : (Q.card : ℂ) ≠ 0 := by exact_mod_cast hcard.ne'
    have heq : (1 : ℂ) - K / (Q.card : ℂ) = -(K - (Q.card : ℂ)) / (Q.card : ℂ) := by
      field_simp
      ring
    rw [heq, norm_div, norm_neg, Complex.norm_natCast]
    exact div_le_div_of_nonneg_right herror (Nat.cast_nonneg _)

