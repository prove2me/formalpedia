-- Prove2me | solution 2 for CallNoCall.OneDir.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T14:24:18.907435+00:00
-- url     : https://prove2.me/submissions/3eb07d2c-9434-4e6d-9dac-088b7b7f204f

import Mathlib
import Definitions.Def_CallNoCall_OneDir_Setting
import Theorems.Thm_CallNoCall_OneDir_avgWait_le_of_rates_le
import Theorems.Thm_CallNoCall_OneDir_rate_comparison

-- carved verbatim out of submission 26fb072a-5b82-44be-8ea2-a30f56b288dd, lines 646-657

section
set_option autoImplicit false
open CallNoCall.OneDir

lemma prodRates_pos (μ : ℕ → ℝ) (hμ : ∀ n, 1 ≤ n → 0 < μ n) (i : ℕ) : 0 < prodRates μ i := by
  unfold prodRates
  apply Finset.prod_pos
  intro j hj
  exact hμ j (Finset.mem_Icc.mp hj).1

lemma prodRates_succ (μ : ℕ → ℝ) (i : ℕ) :
    prodRates μ (i + 1) = prodRates μ i * μ (i + 1) := by
  unfold prodRates
  exact Finset.prod_Icc_succ_top (by omega) _

end

section
set_option autoImplicit false
open CallNoCall.OneDir
open Filter Topology

lemma den_summable (μ : ℕ → ℝ) (hμ : ∀ n, 1 ≤ n → 0 < μ n) (L lam : ℝ) (hL : 0 < L)
    (hlam : 0 < lam) (hlt : lam < L) (hT : Tendsto μ atTop (𝓝 L)) :
    Summable (fun i : ℕ => denTerm μ lam (i + 1)) := by
  have hpos : ∀ i, 0 < denTerm μ lam (i + 1) := fun i => by
    unfold denTerm
    have := prodRates_pos μ hμ (i + 1)
    positivity
  have hT2 : Tendsto (fun i : ℕ => μ (i + 2)) atTop (𝓝 L) := hT.comp (tendsto_add_atTop_nat 2)
  refine summable_of_ratio_test_tendsto_lt_one (l := lam / L) ((div_lt_one hL).2 hlt)
    (Eventually.of_forall (fun i => (hpos i).ne')) ?_
  have : Tendsto (fun i : ℕ => lam / μ (i + 2)) atTop (𝓝 (lam / L)) :=
    tendsto_const_nhds.div hT2 hL.ne'
  refine this.congr (fun i => ?_)
  rw [Real.norm_of_nonneg (hpos (i + 1)).le, Real.norm_of_nonneg (hpos i).le]
  have h1 := prodRates_pos μ hμ (i + 1)
  have h2 := hμ (i + 2) (by omega)
  unfold denTerm
  rw [prodRates_succ μ (i + 1)]
  field_simp
  ring

lemma num_summable (μ : ℕ → ℝ) (hμ : ∀ n, 1 ≤ n → 0 < μ n) (L lam : ℝ) (hL : 0 < L)
    (hlam : 0 < lam) (hlt : lam < L) (hT : Tendsto μ atTop (𝓝 L)) :
    Summable (fun i : ℕ => numTerm μ lam (i + 1)) := by
  have hpos : ∀ i, 0 < numTerm μ lam (i + 1) := fun i => by
    unfold numTerm
    have := prodRates_pos μ hμ (i + 1)
    positivity
  have hT2 : Tendsto (fun i : ℕ => μ (i + 2)) atTop (𝓝 L) := hT.comp (tendsto_add_atTop_nat 2)
  refine summable_of_ratio_test_tendsto_lt_one (l := lam / L) ((div_lt_one hL).2 hlt)
    (Eventually.of_forall (fun i => (hpos i).ne')) ?_
  have h1 : Tendsto (fun i : ℕ => (1 + 1 / ((i : ℝ) + 1)) * (lam / μ (i + 2))) atTop
      (𝓝 ((1 + 0) * (lam / L))) :=
    (tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat).mul
      (tendsto_const_nhds.div hT2 hL.ne')
  simp only [add_zero, one_mul] at h1
  refine h1.congr (fun i => ?_)
  rw [Real.norm_of_nonneg (hpos (i + 1)).le, Real.norm_of_nonneg (hpos i).le]
  have h3 := prodRates_pos μ hμ (i + 1)
  have h2 := hμ (i + 2) (by omega)
  unfold numTerm
  rw [prodRates_succ μ (i + 1)]
  simp only [Nat.add_sub_cancel]
  push_cast
  field_simp
  ring

lemma fw_of_lt (μ : ℕ → ℝ) (hμ : ∀ n, 1 ≤ n → 0 < μ n) (L lam : ℝ) (hL : 0 < L)
    (hlam : 0 ≤ lam) (hlt : lam < L) (hT : Tendsto μ atTop (𝓝 L)) : FiniteWait μ lam := by
  rcases hlam.lt_or_eq with hp | h0
  · exact ⟨num_summable μ hμ L lam hL hp hlt hT, den_summable μ hμ L lam hL hp hlt hT⟩
  · subst h0
    constructor
    · apply summable_of_ne_finset_zero (s := {0})
      intro b hb
      have : b ≠ 0 := by simpa using hb
      simp [numTerm, this]
    · apply summable_of_ne_finset_zero (s := {0})
      intro b hb
      have : b ≠ 0 := by simpa using hb
      simp [denTerm]

lemma not_summable (μ : ℕ → ℝ) (hμ : ∀ n, 1 ≤ n → 0 < μ n) (L lam : ℝ) (hL : 0 < L)
    (hlam : L ≤ lam) (N : ℕ) (hN : ∀ n, N ≤ n → μ n ≤ L) :
    ¬ Summable (fun i : ℕ => denTerm μ lam (i + 1)) := by
  intro hs
  have hlam0 : 0 < lam := lt_of_lt_of_le hL hlam
  have hpos : ∀ i, 0 < denTerm μ lam (i + 1) := fun i => by
    unfold denTerm
    have := prodRates_pos μ hμ (i + 1)
    positivity
  have hmono : ∀ i, N ≤ i → denTerm μ lam (i + 1) ≤ denTerm μ lam (i + 1 + 1) := by
    intro i hi
    have h1 := prodRates_pos μ hμ (i + 1)
    have h2 := hμ (i + 2) (by omega)
    have h3 : μ (i + 2) ≤ lam := le_trans (hN (i + 2) (by omega)) hlam
    unfold denTerm
    rw [prodRates_succ μ (i + 1)]
    rw [pow_succ lam (i + 1), div_le_div_iff₀ h1 (mul_pos h1 h2)]
    have : 0 < lam ^ (i + 1) := pow_pos hlam0 _
    nlinarith [mul_le_mul_of_nonneg_left h3 (mul_pos this h1).le]
  have hge : ∀ i, N ≤ i → denTerm μ lam (N + 1) ≤ denTerm μ lam (i + 1) := by
    intro i hi
    induction i, hi using Nat.le_induction with
    | base => exact le_rfl
    | succ i hi ih => exact ih.trans (hmono i hi)
  have h0 := hs.tendsto_atTop_zero
  have hev := h0.eventually (gt_mem_nhds (hpos N))
  obtain ⟨i, hi1, hi2⟩ := (hev.and (eventually_ge_atTop N)).exists
  exact absurd (hge i hi2) (not_le.2 hi1)

lemma mu1c_eq (d v R : ℝ) (k n : ℕ) (hn : k < n) :
    mu1c d v R k n = (k : ℝ) / (d / v + R / (v * ((n : ℝ) - k + 1))) := by
  rw [mu1c, if_neg (by omega), if_neg (by omega)]

lemma mu1c_pos (d v R : ℝ) (k : ℕ) (hd : 0 < d) (hv : 0 < v) (hR : 0 < R) (hk : 1 ≤ k)
    (n : ℕ) (hn : 1 ≤ n) : 0 < mu1c d v R k n := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
  unfold mu1c
  split_ifs with h1 h2
  · have : (n:ℝ) + 1 ≤ k := by exact_mod_cast h1
    have : (0:ℝ) < (k : ℝ) - n + 1 := by linarith
    positivity
  · positivity
  · have : (k:ℝ) < n := by exact_mod_cast (by omega : k < n)
    have : (0:ℝ) < (n : ℝ) - k + 1 := by linarith
    positivity

lemma mu1c_tendsto (d v R : ℝ) (k : ℕ) (hd : 0 < d) (hv : 0 < v) (hR : 0 < R) (hk : 1 ≤ k) :
    Tendsto (mu1c d v R k) atTop (𝓝 ((k : ℝ) * v / d)) := by
  have hdv : 0 < d / v := by positivity
  have h1 : Tendsto (fun n : ℕ => (n : ℝ) - k + 1) atTop atTop := by
    have : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have := tendsto_atTop_add_const_right atTop (-(k : ℝ) + 1) this
    refine this.congr (fun n => ?_)
    ring
  have h2 : Tendsto (fun n : ℕ => v * ((n : ℝ) - k + 1)) atTop atTop :=
    h1.const_mul_atTop hv
  have h3 : Tendsto (fun n : ℕ => R / (v * ((n : ℝ) - k + 1))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop h2
  have h4 : Tendsto (fun n : ℕ => (k : ℝ) / (d / v + R / (v * ((n : ℝ) - k + 1)))) atTop
      (𝓝 ((k : ℝ) / (d / v + 0))) :=
    tendsto_const_nhds.div (tendsto_const_nhds.add h3) (by rw [add_zero]; exact hdv.ne')
  have h5 : (k : ℝ) / (d / v + 0) = (k : ℝ) * v / d := by
    rw [add_zero]; field_simp
  rw [h5] at h4
  refine h4.congr' ?_
  filter_upwards [eventually_gt_atTop k] with n hn
  exact (mu1c_eq d v R k n hn).symm

lemma mu1c_le (d v R : ℝ) (k : ℕ) (hd : 0 < d) (hv : 0 < v) (hR : 0 < R) (hk : 1 ≤ k)
    (n : ℕ) (hn : k < n) : mu1c d v R k n ≤ (k : ℝ) * v / d := by
  have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hnk : (k:ℝ) < n := by exact_mod_cast hn
  have hdv : 0 < d / v := by positivity
  rw [mu1c_eq d v R k n hn]
  have hpos : (0:ℝ) < (n : ℝ) - k + 1 := by linarith
  have h5 : (k : ℝ) * v / d = (k : ℝ) / (d / v) := by field_simp
  rw [h5]
  apply div_le_div_of_nonneg_left (by positivity) hdv
  have : 0 < R / (v * ((n : ℝ) - k + 1)) := by positivity
  linarith

theorem t11_solution (lam d v R : ℝ) (k : ℕ) (hd : 0 < d) (hv : 0 < v) (hR : 0 < R) (hk : 1 ≤ k)
    (hlam0 : 0 ≤ lam) :
    FiniteWait (mu1c d v R k) lam ↔ lam < k * v / d := by
  have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hL : 0 < (k : ℝ) * v / d := by positivity
  have hpos := mu1c_pos d v R k hd hv hR hk
  constructor
  · intro h
    by_contra hge
    push_neg at hge
    exact not_summable (mu1c d v R k) hpos _ lam hL hge (k + 1)
      (fun n hn => mu1c_le d v R k hd hv hR hk n (by omega)) h.2
  · intro h
    exact fw_of_lt (mu1c d v R k) hpos _ lam hL hlam0 h
      (mu1c_tendsto d v R k hd hv hR hk)

end

section
set_option autoImplicit false
open CallNoCall.OneDir

theorem solution (lam d v R : ℝ) (k : ℕ) (hd : 0 < d) (hv : 0 < v) (hR : 0 < R) (hk : 1 ≤ k)
    (hlam0 : 0 ≤ lam) (hlam : lam < k * v / d) :
    FiniteWait (mu1c d v R k) lam ∧ FiniteWait (muNC lam d v R k) lam ∧
      Wnc lam d v R k ≤ W1c lam d v R k := by
  have h1 : FiniteWait (mu1c d v R k) lam := (t11_solution lam d v R k hd hv hR hk hlam0).2 hlam
  have hpos : ∀ n, 1 ≤ n → 0 < mu1c d v R k n := fun n hn =>
    (CallNoCall.OneDir.rate_comparison lam d v R k hd hv hR hk hlam0 n hn).1
  have hle : ∀ n, 1 ≤ n → mu1c d v R k n ≤ muNC lam d v R k n := fun n hn =>
    (CallNoCall.OneDir.rate_comparison lam d v R k hd hv hR hk hlam0 n hn).2
  obtain ⟨h2, h3⟩ := CallNoCall.OneDir.avgWait_le_of_rates_le (mu1c d v R k) (muNC lam d v R k) lam d v hpos hle hlam0 h1
  exact ⟨h1, h2, h3⟩

end
