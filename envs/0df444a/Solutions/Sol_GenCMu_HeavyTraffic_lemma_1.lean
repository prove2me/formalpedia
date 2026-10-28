-- Prove2me | solution 1 for GenCMu.HeavyTraffic.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T04:08:58.196627+00:00
-- url     : https://prove2.me/submissions/8fca8bae-fc92-4aa9-83fd-c9bea33b4397

import Mathlib
import Definitions.Def_GenCMu_HeavyTraffic_Model

open Filter Topology Finset in
open GenCMu.HeavyTraffic in
theorem solution (a : ℝ) (ha : 0 < a) (x : ℕ → ℕ → ℝ) (hx : ∀ n i, 0 ≤ x n i)
    (Xbar Xtil : ℕ → ℝ → ℝ) (Xbs Xts : ℝ → ℝ)
    (hXbar : ∀ n, ContinuousOn (Xbar n) (Set.Icc 0 a))
    (hbar_lipschitz : ∃ B : ℝ, 0 ≤ B ∧ ∀ n s t, s ∈ Set.Icc (0 : ℝ) a →
      t ∈ Set.Icc (0 : ℝ) a → |Xbar n s - Xbar n t| ≤ B * |s - t|)
    (hXtil : ∀ n, ContinuousOn (Xtil n) (Set.Icc 0 a))
    (hXbs : ContinuousOn Xbs (Set.Icc 0 a)) (hXts : ContinuousOn Xts (Set.Icc 0 a))
    (hbar : TendstoUniformlyOn Xbar Xbs atTop (Set.Icc 0 a))
    (htil : TendstoUniformlyOn Xtil Xts atTop (Set.Icc 0 a))
    (hexp : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ s ∈ Set.Icc (0 : ℝ) a,
      |partialSum (x n) ⌊(n : ℝ) * s⌋₊ - (n * Xbar n s + Real.sqrt n * Xtil n s)|
        ≤ ε * Real.sqrt n) :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ i ∈ Finset.Icc 1 ⌊(n : ℝ) * a⌋₊, x n i ≤ ε * Real.sqrt n := by
  intro ε hε
  obtain ⟨B, hB0, hB⟩ := hbar_lipschitz
  have hη : 0 < ε / 12 := by positivity
  have hunif := (Metric.tendstoUniformlyOn_iff.mp htil) (ε / 12) hη
  have huc := (isCompact_Icc.uniformContinuousOn_of_continuous hXts)
  obtain ⟨δ, hδ, hδc⟩ := Metric.uniformContinuousOn_iff.mp huc (ε / 12) hη
  have hNB : ∀ᶠ n : ℕ in atTop, B ≤ ε / 4 * Real.sqrt n := by
    filter_upwards [eventually_ge_atTop ⌈(4 * B / ε) ^ 2⌉₊] with n hn
    have h1 : (4 * B / ε) ^ 2 ≤ (n : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
    have h2 : 4 * B / ε ≤ Real.sqrt n := Real.le_sqrt_of_sq_le h1
    have h3 : 4 * B / ε * ε = 4 * B := by field_simp
    nlinarith
  have hδn : ∀ᶠ n : ℕ in atTop, 1 / (n : ℝ) < δ := by
    filter_upwards [eventually_gt_atTop ⌈1 / δ⌉₊] with n hn
    have h1 : 1 / δ < (n : ℝ) := lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hn)
    have hn0 : (0 : ℝ) < n := lt_trans (by positivity) h1
    rw [div_lt_iff₀ hn0]
    rw [div_lt_iff₀ hδ] at h1
    linarith
  filter_upwards [hexp (ε / 4) (by positivity), hunif, hNB, hδn, eventually_ge_atTop 1]
    with n h1 h2 h3 h4 h5
  intro i hi
  rw [Finset.mem_Icc] at hi
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hia : (i : ℝ) ≤ n * a := by
    have := Nat.floor_le (show 0 ≤ (n : ℝ) * a by positivity)
    exact le_trans (by exact_mod_cast hi.2) this
  set s1 : ℝ := (i : ℝ) / n with hs1
  set s2 : ℝ := ((i - 1 : ℕ) : ℝ) / n with hs2
  have hi1 : ((i - 1 : ℕ) : ℝ) = (i : ℝ) - 1 := by
    rw [Nat.cast_sub hi.1]; simp
  have hs1m : s1 ∈ Set.Icc (0 : ℝ) a := by
    refine ⟨by positivity, ?_⟩
    rw [hs1, div_le_iff₀ hn0]; linarith
  have hs2m : s2 ∈ Set.Icc (0 : ℝ) a := by
    refine ⟨by positivity, ?_⟩
    rw [hs2, div_le_iff₀ hn0, hi1]; linarith
  have hdiff : s1 - s2 = 1 / n := by
    rw [hs1, hs2, hi1]; field_simp; ring
  have hf1 : ⌊(n : ℝ) * s1⌋₊ = i := by
    rw [hs1, mul_div_cancel₀ _ hn0.ne', Nat.floor_natCast]
  have hf2 : ⌊(n : ℝ) * s2⌋₊ = i - 1 := by
    rw [hs2, mul_div_cancel₀ _ hn0.ne', Nat.floor_natCast]
  have e1 := h1 s1 hs1m
  have e2 := h1 s2 hs2m
  rw [hf1] at e1
  rw [hf2] at e2
  have hps : partialSum (x n) i = partialSum (x n) (i - 1) + x n i := by
    unfold partialSum
    conv_lhs => rw [show i = (i - 1) + 1 by omega]
    rw [Finset.sum_Icc_succ_top (by omega), show i - 1 + 1 = i by omega]
  -- Lipschitz bound for the fluid part
  have hlip := hB n s1 s2 hs1m hs2m
  rw [hdiff, abs_of_pos (by positivity : (0:ℝ) < 1 / n)] at hlip
  have hbarb : (n : ℝ) * (Xbar n s1 - Xbar n s2) ≤ B := by
    have := mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) hlip) hn0.le
    have e : (n : ℝ) * (B * (1 / n)) = B := by field_simp
    linarith
  -- diffusion part
  have d1 := h2 s1 hs1m
  have d2 := h2 s2 hs2m
  have dc : dist (Xts s1) (Xts s2) < ε / 12 := by
    apply hδc s1 hs1m s2 hs2m
    rw [Real.dist_eq, hdiff, abs_of_pos (by positivity : (0:ℝ) < 1 / n)]
    exact h4
  rw [Real.dist_eq] at d1 d2 dc
  have htilb : Xtil n s1 - Xtil n s2 ≤ ε / 4 := by
    have := (abs_lt.mp d1); have := (abs_lt.mp d2); have := (abs_lt.mp dc)
    linarith
  have hsq : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have htilb' := mul_le_mul_of_nonneg_left htilb hsq
  obtain ⟨e1a, e1b⟩ := abs_le.mp e1
  obtain ⟨e2a, e2b⟩ := abs_le.mp e2
  nlinarith
