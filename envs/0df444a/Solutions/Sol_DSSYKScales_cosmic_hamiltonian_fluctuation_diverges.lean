-- Prove2me | solution 1 for DSSYKScales.cosmic_hamiltonian_fluctuation_diverges
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:14:15.411528+00:00
-- url     : https://prove2.me/submissions/4c6309c9-aa41-4f31-87a0-6b7c2b445818

import Mathlib
import Definitions.Def_DSSYKScales_defs

open Filter Topology

namespace DSSYKScales

lemma aux_chd_sum_range (q : ℕ) :
    ∑ i ∈ Finset.range q, (i : ℝ) = (q : ℝ) * ((q : ℝ) - 1) / 2 := by
  induction q with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma aux_chd_ratio (N q : ℕ) (J : ℝ) (hq : 1 ≤ q) (hqN : q ≤ N) (hN : 0 < N) :
    cosmicHamiltonianSecondMoment N q J / (N : ℝ) =
      J ^ 2 * ∏ i ∈ Finset.range q, (((N : ℝ) - i) / N) := by
  unfold cosmicHamiltonianSecondMoment
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have h1 : ((N.choose q : ℕ) : ℝ) * (q.factorial : ℝ) =
      ∏ i ∈ Finset.range q, ((N : ℝ) - i) := by
    rw [← Nat.cast_mul, mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose,
      Nat.descFactorial_eq_prod_range]
    push_cast
    apply Finset.prod_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [Nat.cast_sub (by omega)]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range, ← h1]
  have : (N:ℝ) ^ q = (N:ℝ) ^ (q - 1) * N := by
    rw [← pow_succ]; congr 1; omega
  rw [this]
  field_simp

lemma aux_chd_factor_upper (N i : ℝ) (hN : 0 < N) : (N - i) / N ≤ Real.exp (-(i / N)) := by
  have h := Real.add_one_le_exp (-(i / N))
  have e : (N - i) / N = -(i / N) + 1 := by field_simp; ring
  rw [e]; exact h

lemma aux_chd_factor_lower (N q i : ℝ) (hi0 : 0 ≤ i) (hiq : i ≤ q) (hqN : q < N) :
    Real.exp (-(i / (N - q))) ≤ (N - i) / N := by
  have hNq : 0 < N - q := by linarith
  have hNi : 0 < N - i := by linarith
  have hN : 0 < N := by linarith
  have step1 : Real.exp (-(i / (N - q))) ≤ Real.exp (-(i / (N - i))) := by
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    exact div_le_div_of_nonneg_left hi0 hNq (by linarith)
  have step2 : Real.exp (-(i / (N - i))) ≤ (N - i) / N := by
    have h := Real.add_one_le_exp (i / (N - i))
    have e : i / (N - i) + 1 = N / (N - i) := by field_simp; ring
    rw [e] at h
    rw [Real.exp_neg]
    have h2 := inv_anti₀ (by positivity) h
    rw [inv_div] at h2
    exact h2
  exact step1.trans step2

lemma aux_chd_prod_bounds (N q : ℕ) (hqN : (q:ℝ) < N) :
    Real.exp (-(((q:ℝ) * ((q:ℝ) - 1) / 2) / ((N:ℝ) - q))) ≤
      ∏ i ∈ Finset.range q, (((N : ℝ) - i) / N) ∧
    ∏ i ∈ Finset.range q, (((N : ℝ) - i) / N) ≤
      Real.exp (-(((q:ℝ) * ((q:ℝ) - 1) / 2) / N)) := by
  have hN : (0:ℝ) < N := by linarith [(Nat.cast_nonneg q : (0:ℝ) ≤ q)]
  constructor
  · calc Real.exp (-(((q:ℝ) * ((q:ℝ) - 1) / 2) / ((N:ℝ) - q)))
        = ∏ i ∈ Finset.range q, Real.exp (-((i:ℝ) / ((N:ℝ) - q))) := by
          rw [← Real.exp_sum, Finset.sum_neg_distrib, ← Finset.sum_div, aux_chd_sum_range]
      _ ≤ _ := by
          apply Finset.prod_le_prod
          · intro i _; exact (Real.exp_pos _).le
          · intro i hi
            rw [Finset.mem_range] at hi
            have : (i:ℝ) ≤ q := by exact_mod_cast hi.le
            exact aux_chd_factor_lower N q i (Nat.cast_nonneg i) this hqN
  · calc ∏ i ∈ Finset.range q, (((N : ℝ) - i) / N)
        ≤ ∏ i ∈ Finset.range q, Real.exp (-((i:ℝ) / N)) := by
          apply Finset.prod_le_prod
          · intro i hi
            rw [Finset.mem_range] at hi
            have : (i:ℝ) ≤ q := by exact_mod_cast hi.le
            apply div_nonneg _ hN.le; linarith
          · intro i _; exact aux_chd_factor_upper N i hN
      _ = _ := by
          rw [← Real.exp_sum, Finset.sum_neg_distrib, ← Finset.sum_div, aux_chd_sum_range]

end DSSYKScales

open DSSYKScales

theorem solution (N q : ℕ → ℕ) (lam J : ℝ) (hJ : J ≠ 0)
    (hlim : IsDoubleScaledLimit N q lam) :
    Tendsto (fun n => cosmicHamiltonianSecondMoment (N n) (q n) J / (N n : ℝ))
      atTop (𝓝 (J ^ 2 * Real.exp (-(lam / 2)))) ∧
    Tendsto (fun n => cosmicHamiltonianSecondMoment (N n) (q n) J) atTop atTop := by
  obtain ⟨hlam, hN, hf⟩ := hlim
  set f : ℕ → ℝ := fun n => ((q n : ℝ) ^ 2) / (N n : ℝ) with hfdef
  set g : ℕ → ℝ := fun n => (q n : ℝ) / (N n : ℝ) with hgdef
  have hNinv : Tendsto (fun n => ((N n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hN
  have hN1 : ∀ᶠ n in atTop, (1:ℝ) ≤ N n := hN.eventually_ge_atTop 1
  have hg2 : Tendsto (fun n => g n ^ 2) atTop (𝓝 0) := by
    have : Tendsto (fun n => f n * ((N n : ℝ))⁻¹) atTop (𝓝 (lam * 0)) := hf.mul hNinv
    rw [mul_zero] at this
    apply this.congr'
    filter_upwards [hN1] with n hn
    have : (N n : ℝ) ≠ 0 := by linarith
    simp only [hfdef, hgdef]
    field_simp
  have hg : Tendsto g atTop (𝓝 0) := by
    have h := hg2.sqrt
    rw [Real.sqrt_zero] at h
    apply h.congr'
    filter_upwards with n
    rw [Real.sqrt_sq]
    simp only [hgdef]; positivity
  have hfpos : ∀ᶠ n in atTop, 0 < f n := hf.eventually (lt_mem_nhds hlam)
  have hghalf : ∀ᶠ n in atTop, g n < 1 / 2 := hg.eventually (gt_mem_nhds (by norm_num))
  have hU : Tendsto (fun n => (f n - g n) / 2) atTop (𝓝 (lam / 2)) := by
    have := (hf.sub hg).div_const 2
    simpa using this
  have hL : Tendsto (fun n => ((f n - g n) / 2) / (1 - g n)) atTop (𝓝 (lam / 2)) := by
    have := hU.div ((tendsto_const_nhds (x := (1:ℝ))).sub hg) (by norm_num)
    simp only [sub_zero, div_one] at this
    exact this
  have hqN : ∀ᶠ n in atTop, (q n : ℝ) < N n := by
    filter_upwards [hN1, hghalf] with n hn hgh
    have hNp : (0:ℝ) < N n := by linarith
    simp only [hgdef] at hgh
    rw [div_lt_iff₀ hNp] at hgh
    linarith
  have hP : Tendsto (fun n => ∏ i ∈ Finset.range (q n), (((N n : ℝ) - i) / N n)) atTop
      (𝓝 (Real.exp (-(lam / 2)))) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      ((Real.continuous_exp.tendsto _).comp hL.neg)
      ((Real.continuous_exp.tendsto _).comp hU.neg)
    · filter_upwards [hN1, hqN] with n hn hlt
      have hb := (aux_chd_prod_bounds (N n) (q n) hlt).1
      have hNne : (N n : ℝ) ≠ 0 := by linarith
      have hNq : (N n : ℝ) - q n ≠ 0 := by linarith
      have e : ((f n - g n) / 2) / (1 - g n) =
          ((q n : ℝ) * ((q n : ℝ) - 1) / 2) / ((N n : ℝ) - q n) := by
        simp only [hfdef, hgdef]
        have h1 : 1 - (q n : ℝ) / N n = ((N n : ℝ) - q n) / N n := by field_simp
        rw [h1]
        field_simp
      simp only [Function.comp]
      rw [e]
      exact hb
    · filter_upwards [hN1, hqN] with n hn hlt
      have hb := (aux_chd_prod_bounds (N n) (q n) hlt).2
      have hNne : (N n : ℝ) ≠ 0 := by linarith
      have e : (f n - g n) / 2 = ((q n : ℝ) * ((q n : ℝ) - 1) / 2) / N n := by
        simp only [hfdef, hgdef]
        field_simp
      simp only [Function.comp]
      rw [e]
      exact hb
  have hC : 0 < J ^ 2 * Real.exp (-(lam / 2)) := by
    have : 0 < J ^ 2 := by positivity
    exact mul_pos this (Real.exp_pos _)
  have h1 : Tendsto (fun n => cosmicHamiltonianSecondMoment (N n) (q n) J / (N n : ℝ))
      atTop (𝓝 (J ^ 2 * Real.exp (-(lam / 2)))) := by
    apply (tendsto_const_nhds.mul hP).congr'
    filter_upwards [hN1, hqN, hfpos] with n hn hlt hfp
    have hq1 : 1 ≤ q n := by
      rcases Nat.eq_zero_or_pos (q n) with h | h
      · exfalso
        simp only [hfdef, h] at hfp
        simp at hfp
      · exact h
    have hqN' : q n ≤ N n := by
      have : (q n : ℝ) ≤ N n := hlt.le
      exact_mod_cast this
    have hNpos : 0 < N n := by
      have : (0:ℝ) < N n := by linarith
      exact_mod_cast this
    rw [aux_chd_ratio (N n) (q n) J hq1 hqN' hNpos]
  refine ⟨h1, ?_⟩
  apply (h1.pos_mul_atTop hC hN).congr'
  filter_upwards [hN1] with n hn
  have hNne : (N n : ℝ) ≠ 0 := by linarith
  field_simp
