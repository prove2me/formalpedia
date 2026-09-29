-- Prove2me | solution 1 for Complex.exists_forall_norm_digamma_le_mul_log_of_le_re
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/fbcbf70a-59db-5298-adfc-52fa8848bf72

import Mathlib
import Theorems.Thm_Complex_hasSum_one_div_add_one_sub_one_div_add_eq_digamma_add_eulerMascheroniConstant
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Complex_exists_forall_norm_digamma_le_mul_log_of_le_re

set_option autoImplicit false

namespace SlDigammaStrip

open Finset

noncomputable def term (s : ℂ) (k : ℕ) : ℂ := 1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + s)

theorem re_natCast_add (s : ℂ) (k : ℕ) : ((k : ℂ) + s).re = (k : ℝ) + s.re := by simp

theorem le_norm_natCast_add (s : ℂ) (k : ℕ) : (k : ℝ) + s.re ≤ ‖(k : ℂ) + s‖ := by
  rw [← re_natCast_add]; exact Complex.re_le_norm _

theorem le_norm_natCast_add_one (k : ℕ) : (k : ℝ) + 1 ≤ ‖(k : ℂ) + 1‖ := by
  have := le_norm_natCast_add 1 k
  simpa using this

theorem norm_term_le_head {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {s : ℂ} (hs : δ ≤ s.re) (k : ℕ) :
    ‖term s k‖ ≤ (1 + δ⁻¹) / ((k : ℝ) + 1) := by
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hn1 : (k : ℝ) + 1 ≤ ‖(k : ℂ) + 1‖ := le_norm_natCast_add_one k
  have hns : (k : ℝ) + δ ≤ ‖(k : ℂ) + s‖ := le_trans (by linarith) (le_norm_natCast_add s k)
  have hkδ : (0 : ℝ) < (k : ℝ) + δ := by positivity
  have h1 : ‖(1 : ℂ) / ((k : ℂ) + 1)‖ ≤ 1 / ((k : ℝ) + 1) := by
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le hk hn1
  have h2 : ‖(1 : ℂ) / ((k : ℂ) + s)‖ ≤ δ⁻¹ / ((k : ℝ) + 1) := by
    rw [norm_div, norm_one]
    calc 1 / ‖(k : ℂ) + s‖ ≤ 1 / ((k : ℝ) + δ) := one_div_le_one_div_of_le hkδ hns
      _ ≤ δ⁻¹ / ((k : ℝ) + 1) := by
        rw [div_le_div_iff₀ hkδ hk, inv_mul_eq_div, le_div_iff₀ hδ]
        nlinarith [mul_le_of_le_one_right hk0 hδ1]
  calc ‖term s k‖ ≤ ‖(1 : ℂ) / ((k : ℂ) + 1)‖ + ‖(1 : ℂ) / ((k : ℂ) + s)‖ := norm_sub_le _ _
    _ ≤ 1 / ((k : ℝ) + 1) + δ⁻¹ / ((k : ℝ) + 1) := add_le_add h1 h2
    _ = (1 + δ⁻¹) / ((k : ℝ) + 1) := by ring

theorem norm_term_le_tail {s : ℂ} (hs : 0 < s.re) {k : ℕ} (hk : 1 ≤ k) :
    ‖term s k‖ ≤ ‖s - 1‖ * (1 / (k : ℝ) - 1 / ((k : ℝ) + 1)) := by
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
  have hn1 : (k : ℝ) + 1 ≤ ‖(k : ℂ) + 1‖ := le_norm_natCast_add_one k
  have hns : (k : ℝ) ≤ ‖(k : ℂ) + s‖ := le_trans (by linarith) (le_norm_natCast_add s k)
  have hne1 : ((k : ℂ) + 1) ≠ 0 := fun h => by
    have := hn1; rw [h, norm_zero] at this; linarith
  have hnes : ((k : ℂ) + s) ≠ 0 := fun h => by
    have := hns; rw [h, norm_zero] at this; linarith
  have heq : term s k = (s - 1) / (((k : ℂ) + 1) * ((k : ℂ) + s)) := by
    unfold term
    field_simp
    ring
  rw [heq, norm_div, norm_mul]
  have hden : (k : ℝ) + 1 ≤ ‖(k : ℂ) + 1‖ := hn1
  calc ‖s - 1‖ / (‖(k : ℂ) + 1‖ * ‖(k : ℂ) + s‖) ≤ ‖s - 1‖ / (((k : ℝ) + 1) * (k : ℝ)) := by
        apply div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
        exact mul_le_mul hn1 hns hkpos.le (norm_nonneg _)
    _ = ‖s - 1‖ * (1 / (k : ℝ) - 1 / ((k : ℝ) + 1)) := by
        field_simp
        ring

theorem sum_Ico_one_div_sub (N : ℕ) (hN : 1 ≤ N) (m : ℕ) (hm : N ≤ m) :
    ∑ k ∈ Ico N m, (1 / (k : ℝ) - 1 / ((k : ℝ) + 1)) = 1 / (N : ℝ) - 1 / (m : ℝ) := by
  induction m, hm using Nat.le_induction with
  | base => simp
  | succ m hNm ih =>
    rw [Finset.sum_Ico_succ_top hNm, ih]
    push_cast
    ring

theorem sum_range_one_div_le (N : ℕ) : ∑ i ∈ range N, (1 : ℝ) / ((i : ℝ) + 1) ≤ 1 + Real.log N := by
  have h := harmonic_le_one_add_log N
  have e : ((harmonic N : ℚ) : ℝ) = ∑ i ∈ range N, (1 : ℝ) / ((i : ℝ) + 1) := by
    simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_add, Rat.cast_one, Rat.cast_natCast, Nat.cast_add,
      Nat.cast_one, one_div]
  rw [← e]
  exact h

theorem sum_norm_term_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {s : ℂ} (hs : δ ≤ s.re) (hs2 : s.re ≤ 2)
    (n : ℕ) :
    ∑ k ∈ range n, ‖term s k‖ ≤ (1 + δ⁻¹) * (1 + Real.log (2 + |s.im|)) + 1 := by
  have hre : 0 < s.re := lt_of_lt_of_le hδ hs
  set R : ℝ := ‖s - 1‖ with hR
  set N : ℕ := ⌊R⌋₊ + 1 with hN
  have hR0 : 0 ≤ R := norm_nonneg _
  have hN1 : 1 ≤ N := Nat.le_add_left 1 _
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hRN : R < (N : ℝ) := by
    rw [hN]; push_cast; exact Nat.lt_floor_add_one R
  have hRle : R ≤ 1 + |s.im| := by
    have h1 := Complex.norm_le_abs_re_add_abs_im (s - 1)
    have h2 : |(s - 1).re| ≤ 1 := by
      rw [Complex.sub_re, Complex.one_re, abs_le]; constructor <;> linarith
    have h3 : (s - 1).im = s.im := by simp
    rw [h3] at h1
    linarith
  have hNle : (N : ℝ) ≤ 2 + |s.im| := by
    rw [hN]; push_cast
    have := Nat.floor_le hR0
    linarith
  have hlogN : Real.log N ≤ Real.log (2 + |s.im|) := Real.log_le_log hNpos hNle
  have hc1 : 0 ≤ 1 + δ⁻¹ := by positivity

  have hhead : ∑ k ∈ range N, ‖term s k‖ ≤ (1 + δ⁻¹) * (1 + Real.log (2 + |s.im|)) := by
    calc ∑ k ∈ range N, ‖term s k‖ ≤ ∑ k ∈ range N, (1 + δ⁻¹) / ((k : ℝ) + 1) :=
          Finset.sum_le_sum fun k _ => norm_term_le_head hδ hδ1 hs k
      _ = (1 + δ⁻¹) * ∑ k ∈ range N, (1 : ℝ) / ((k : ℝ) + 1) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
      _ ≤ (1 + δ⁻¹) * (1 + Real.log N) := mul_le_mul_of_nonneg_left (sum_range_one_div_le N) hc1
      _ ≤ (1 + δ⁻¹) * (1 + Real.log (2 + |s.im|)) := by gcongr

  have htail : ∀ m, N ≤ m → ∑ k ∈ Ico N m, ‖term s k‖ ≤ 1 := by
    intro m hm
    have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast lt_of_lt_of_le hN1 hm
    calc ∑ k ∈ Ico N m, ‖term s k‖ ≤ ∑ k ∈ Ico N m, R * (1 / (k : ℝ) - 1 / ((k : ℝ) + 1)) :=
          Finset.sum_le_sum fun k hk => norm_term_le_tail hre (le_trans hN1 (Finset.mem_Ico.mp hk).1)
      _ = R * (1 / (N : ℝ) - 1 / (m : ℝ)) := by rw [← Finset.mul_sum, sum_Ico_one_div_sub N hN1 m hm]
      _ ≤ R * (1 / (N : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ hR0
          have : 0 ≤ 1 / (m : ℝ) := by positivity
          linarith
      _ ≤ 1 := by
          rw [mul_one_div, div_le_one hNpos]
          exact hRN.le
  have hnn : ∀ k, 0 ≤ ‖term s k‖ := fun k => norm_nonneg _
  rcases Nat.lt_or_ge n N with hnN | hNn
  swap
  · rw [← Finset.sum_range_add_sum_Ico _ hNn]
    linarith [hhead, htail n hNn]
  · have hsub : ∑ k ∈ range n, ‖term s k‖ ≤ ∑ k ∈ range N, ‖term s k‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hnN.le) fun k _ _ => hnn k
    linarith [hhead]

theorem main (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, δ ≤ s.re → s.re ≤ 2 →
      ‖Complex.digamma s‖ ≤ C * Real.log (2 + |s.im|) := by
  set δ₁ : ℝ := min δ 1 with hδ₁
  have hδ₁pos : 0 < δ₁ := lt_min hδ one_pos
  have hδ₁1 : δ₁ ≤ 1 := min_le_right _ _
  set c₁ : ℝ := 1 + δ₁⁻¹ with hc₁
  have hc₁0 : 0 ≤ c₁ := by positivity
  refine ⟨3 * c₁ + 4, by positivity, fun s hs hs2 => ?_⟩
  have hs₁ : δ₁ ≤ s.re := le_trans (min_le_left _ _) hs
  have hre : 0 < s.re := lt_of_lt_of_le hδ₁pos hs₁
  set L : ℝ := Real.log (2 + |s.im|) with hL
  have hL2 : Real.log 2 ≤ L := Real.log_le_log two_pos (by linarith [abs_nonneg s.im])
  have hlog2 : (1 : ℝ) / 2 < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hLhalf : 1 / 2 ≤ L := hlog2.le.trans hL2

  have hser := Complex.hasSum_one_div_add_one_sub_one_div_add_eq_digamma_add_eulerMascheroniConstant s hre
  have hbd : ∀ n, ∑ k ∈ range n, ‖term s k‖ ≤ c₁ * (1 + L) + 1 := fun n =>
    sum_norm_term_le hδ₁pos hδ₁1 hs₁ hs2 n
  have hsum : Summable fun k => ‖term s k‖ := summable_of_sum_range_le (fun k => norm_nonneg _) hbd
  have htsum : ∑' k, ‖term s k‖ ≤ c₁ * (1 + L) + 1 := Real.tsum_le_of_sum_range_le (fun k => norm_nonneg _) hbd
  have heq : Complex.digamma s + (Real.eulerMascheroniConstant : ℂ) = ∑' k, term s k := hser.tsum_eq.symm
  have hn1 : ‖Complex.digamma s + (Real.eulerMascheroniConstant : ℂ)‖ ≤ c₁ * (1 + L) + 1 := by
    rw [heq]
    exact (norm_tsum_le_tsum_norm hsum).trans htsum
  have hγ : ‖(Real.eulerMascheroniConstant : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor
    · linarith [Real.one_half_lt_eulerMascheroniConstant]
    · linarith [Real.eulerMascheroniConstant_lt_two_thirds]
  have hψ : ‖Complex.digamma s‖ ≤ c₁ * (1 + L) + 2 := by
    have := norm_sub_le (Complex.digamma s + (Real.eulerMascheroniConstant : ℂ)) (Real.eulerMascheroniConstant : ℂ)
    rw [add_sub_cancel_right] at this
    linarith
  calc ‖Complex.digamma s‖ ≤ c₁ * (1 + L) + 2 := hψ
    _ ≤ (3 * c₁ + 4) * L := by nlinarith

end SlDigammaStrip

theorem solution
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, δ ≤ s.re → s.re ≤ 2 →
      ‖Complex.digamma s‖ ≤ C * Real.log (2 + |s.im|) :=
  SlDigammaStrip.main δ hδ

end S_Complex_exists_forall_norm_digamma_le_mul_log_of_le_re
end P2MW
export P2MW.S_Complex_exists_forall_norm_digamma_le_mul_log_of_le_re (solution)
