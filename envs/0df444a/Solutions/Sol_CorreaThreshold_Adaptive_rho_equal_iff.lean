-- Prove2me | solution 1 for CorreaThreshold.Adaptive.rho_equal_iff
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T02:40:51.823388+00:00
-- url     : https://prove2.me/submissions/54f1a194-2f1f-4d83-bdb3-e2dcc635d02e

import Mathlib
import Definitions.Def_CorreaThreshold_Adaptive_Setting

namespace Aux_CTA_rho

open CorreaThreshold.Adaptive

lemma intpow (a b : ℝ) (k : ℕ) :
    ∫ q in a..b, (1 - q) ^ k = ((1 - a) ^ (k + 1) - (1 - b) ^ (k + 1)) / (k + 1) := by
  rw [intervalIntegral.integral_comp_sub_left (fun x => x ^ k) 1, integral_pow]

lemma gam_closed {n : ℕ} (hn : 2 ≤ n) (ε : ℕ → ℝ) (i : ℕ) :
    gam n ε (i + 1) = (1 - ε i) ^ (n - 1) - (1 - ε (i + 1)) ^ (n - 1) := by
  unfold gam psi
  rw [Nat.add_sub_cancel, intervalIntegral.integral_const_mul, intpow]
  have h1 : n - 2 + 1 = n - 1 := by omega
  have h2 : (((n - 2 : ℕ) : ℝ) + 1) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn]; push_cast; ring
  have h3 : (n : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rw [h1, h2]
  field_simp

lemma int_closed {n : ℕ} (hn : 2 ≤ n) (a b : ℝ) :
    ∫ q in a..b, psi n q * (1 - q) = ((n : ℝ) - 1) / n * ((1 - a) ^ n - (1 - b) ^ n) := by
  unfold psi
  have e : ∀ q : ℝ, ((n : ℝ) - 1) * (1 - q) ^ (n - 2) * (1 - q) = ((n : ℝ) - 1) * (1 - q) ^ (n - 1) := by
    intro q
    rw [mul_assoc, ← pow_succ, show n - 2 + 1 = n - 1 by omega]
  simp only [e]
  rw [intervalIntegral.integral_const_mul, intpow, show n - 1 + 1 = n by omega]
  have h2 : (((n - 1 : ℕ) : ℝ) + 1) = (n : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]; push_cast; ring
  rw [h2]
  ring

end Aux_CTA_rho

open MeasureTheory ProbabilityTheory CorreaThreshold.Adaptive Aux_CTA_rho in
theorem solution {n : ℕ} (hn : 2 ≤ n) (ε : ℕ → ℝ) (hε0 : ε 0 = 0) (hεn : ε n = 1)
    (hεmono : ∀ i < n, ε i < ε (i + 1)) :
    ((∀ i ∈ Finset.Icc 1 n, rho n ε i = rho n ε 1) ↔
      ∀ i ∈ Finset.Icc 1 (n - 1), gam n ε (i + 1) = ∫ q in ε (i - 1)..ε i, psi n q * (1 - q)) ∧
    ((∀ i ∈ Finset.Icc 1 n, rho n ε i = rho n ε 1) ↔
      ∀ i ∈ Finset.Icc 1 (n - 1),
        ((n : ℝ) - 1) / n * ((1 - ε (i - 1)) ^ n - (1 - ε i) ^ n) =
          (1 - ε i) ^ (n - 1) - (1 - ε (i + 1)) ^ (n - 1)) ∧
    gam n ε 1 = 1 - (1 - ε 1) ^ (n - 1) := by
  -- range of ε
  have hle : ∀ i j, i ≤ j → j ≤ n → ε i ≤ ε j := by
    intro i j hij hjn
    induction j, hij using Nat.le_induction with
    | base => exact le_refl _
    | succ j hij ih => exact le_trans (ih (by omega)) (hεmono j (by omega)).le
  have hε1 : ∀ i, i ≤ n → ε i ≤ 1 := fun i hi => hεn ▸ hle i n hi le_rfl
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  -- positivity of the pieces
  have hγpos : ∀ k, k + 1 ≤ n → 0 < gam n ε (k + 1) := by
    intro k hk
    unfold gam
    rw [Nat.add_sub_cancel]
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
    · exact (by unfold psi; fun_prop : Continuous (psi n)).intervalIntegrable _ _
    · intro x hx
      unfold psi
      have : x < 1 := lt_of_lt_of_le hx.2 (hε1 (k + 1) hk)
      have : 0 < (1 - x) ^ (n - 2) := pow_pos (by linarith) _
      positivity
    · exact hεmono k (by omega)
  have hIpos : ∀ k, k + 1 ≤ n → 0 < ∫ q in ε k..ε (k + 1), psi n q * (1 - q) := by
    intro k hk
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
    · exact (by unfold psi; fun_prop : Continuous (fun q => psi n q * (1 - q))).intervalIntegrable _ _
    · intro x hx
      unfold psi
      have hx1 : x < 1 := lt_of_lt_of_le hx.2 (hε1 (k + 1) hk)
      have : 0 < (1 - x) ^ (n - 2) := pow_pos (by linarith) _
      have : 0 < 1 - x := by linarith
      positivity
    · exact hεmono k (by omega)
  have hrec : ∀ j, rho n ε (j + 2) =
      rho n ε (j + 1) / gam n ε (j + 2) * ∫ q in ε j..ε (j + 1), psi n q * (1 - q) :=
    fun j => rfl
  have hρpos : ∀ i, 1 ≤ i → i ≤ n → 0 < rho n ε i := by
    intro i hi hin
    induction i, hi using Nat.le_induction with
    | base =>
      show 0 < 1 / gam n ε 1
      have := hγpos 0 (by omega)
      positivity
    | succ i hi ih =>
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      rw [hrec j]
      have h1 := ih (by omega)
      have h2 := hγpos (j + 1) (by omega)
      have h3 := hIpos j (by omega)
      positivity
  have part1 : (∀ i ∈ Finset.Icc 1 n, rho n ε i = rho n ε 1) ↔
      ∀ i ∈ Finset.Icc 1 (n - 1), gam n ε (i + 1) = ∫ q in ε (i - 1)..ε i, psi n q * (1 - q) := by
    constructor
    · intro h i hi
      rw [Finset.mem_Icc] at hi
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      rw [Nat.add_sub_cancel]
      have e1 := h (j + 2) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      have e2 := h (j + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      rw [hrec j, ← e2] at e1
      have hr := hρpos (j + 1) (by omega) (by omega)
      have hg := hγpos (j + 1) (by omega)
      field_simp at e1
      linarith
    · intro h i hi
      rw [Finset.mem_Icc] at hi
      obtain ⟨hi1, hin⟩ := hi
      induction i, hi1 using Nat.le_induction with
      | base => rfl
      | succ i hi ih =>
        obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        rw [hrec j, ← ih (by omega)]
        have hh := h (j + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
        rw [Nat.add_sub_cancel] at hh
        rw [← hh]
        have hg := hγpos (j + 1) (by omega)
        field_simp
  refine ⟨part1, part1.trans ?_, ?_⟩
  · refine forall₂_congr fun i hi => ?_
    rw [Finset.mem_Icc] at hi
    rw [gam_closed hn ε i, int_closed hn]
    exact eq_comm
  · have := gam_closed hn ε 0
    rw [hε0] at this
    simpa using this
