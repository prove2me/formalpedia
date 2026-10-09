-- Prove2me | solution 1 for AzumaWeightedSums.StrongLaw.block_sequence_exists
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T17:47:53.63575+00:00
-- url     : https://prove2.me/submissions/a800dd41-e90b-4135-a280-1d7c1bf9e0ee

import Mathlib
import Definitions.Def_AzumaWeightedSums_StrongLaw_ReversedSum

namespace BS22e216a2

open AzumaWeightedSums.StrongLaw Filter

theorem A_succ (a : ℕ → ℝ) (n : ℕ) : A a (n + 1) = A a n + a (n + 1) := by
  unfold A
  rw [Finset.sum_Icc_succ_top (by omega)]

theorem A_zero (a : ℕ → ℝ) : A a 0 = 0 := by simp [A]

theorem A_mono (a : ℕ → ℝ) (ha_pos : ∀ n : ℕ, 1 ≤ n → 0 < a n) {m n : ℕ} (h : m ≤ n) :
    A a m ≤ A a n := by
  unfold A
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    simp only [Finset.mem_Icc] at hx ⊢
    omega
  · intro i hi _
    simp only [Finset.mem_Icc] at hi
    exact (ha_pos i hi.1).le

theorem A_nonneg (a : ℕ → ℝ) (ha_pos : ∀ n : ℕ, 1 ≤ n → 0 < a n) (n : ℕ) : 0 ≤ A a n := by
  have := A_mono a ha_pos (Nat.zero_le n)
  rwa [A_zero] at this

theorem A_strict (a : ℕ → ℝ) (ha_pos : ∀ n : ℕ, 1 ≤ n → 0 < a n) {m n : ℕ} (h : m < n) :
    A a m < A a n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [A_succ]
  have := A_mono a ha_pos (show m ≤ k by omega)
  have := ha_pos (k + 1) (by omega)
  linarith

theorem a_ge_a1 (a : ℕ → ℝ) (ha_mono : ∀ n : ℕ, 1 ≤ n → a n ≤ a (n + 1)) (n : ℕ) (hn : 1 ≤ n) :
    a 1 ≤ a n := by
  induction n, hn using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih => exact ih.trans (ha_mono k hk)

theorem A_ge (a : ℕ → ℝ) (ha_mono : ∀ n : ℕ, 1 ≤ n → a n ≤ a (n + 1)) (n : ℕ) :
    (n : ℝ) * a 1 ≤ A a n := by
  unfold A
  have : ∑ j ∈ Finset.Icc 1 n, a 1 ≤ ∑ j ∈ Finset.Icc 1 n, a j := by
    apply Finset.sum_le_sum
    intro j hj
    simp only [Finset.mem_Icc] at hj
    exact a_ge_a1 a ha_mono j hj.1
  simpa using this

theorem A_tendsto (a : ℕ → ℝ) (ha_pos : ∀ n : ℕ, 1 ≤ n → 0 < a n)
    (ha_mono : ∀ n : ℕ, 1 ≤ n → a n ≤ a (n + 1)) : Tendsto (A a) atTop atTop := by
  have h1 : 0 < a 1 := ha_pos 1 le_rfl
  have : Tendsto (fun n : ℕ => (n : ℝ) * a 1) atTop atTop :=
    Tendsto.atTop_mul_const h1 tendsto_natCast_atTop_atTop
  exact tendsto_atTop_mono (A_ge a ha_mono) this

end BS22e216a2

open AzumaWeightedSums.StrongLaw Filter Asymptotics in
theorem solution (a : ℕ → ℝ) (ha_pos : ∀ n : ℕ, 1 ≤ n → 0 < a n)
    (ha_mono : ∀ n : ℕ, 1 ≤ n → a n ≤ a (n + 1))
    (h49 : (fun n => a n / A a n) =o[atTop] (fun n => 1 / Real.log (Real.log (A a n))))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ nk : ℕ → ℕ, (∀ k : ℕ, 1 ≤ k → 1 ≤ nk k ∧ nk k < nk (k + 1)) ∧
      2 * (3 + ε) / (6 + ε) < A a (nk 1) ∧
      (∀ n : ℕ, nk 1 < n → a n / A a n < ε / (6 + ε)) ∧
      (∀ n : ℕ, nk 1 < n → a n * Real.log (Real.log (A a n)) / A a n < ε ^ 2 / 64) ∧
      (∀ k : ℕ, 2 ≤ k →
        A a (nk (k - 1)) < A a (nk k) ∧ A a (nk k) ≤ (1 + ε / 3) * A a (nk (k - 1)) ∧
          (1 + ε / 3) * A a (nk (k - 1)) < A a (nk k + 1)) := by
  have hAt := BS22e216a2.A_tendsto a ha_pos ha_mono
  have hLL : Tendsto (fun n => Real.log (Real.log (A a n))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp hAt)
  set c : ℝ := min (ε ^ 2 / 128) (ε / (2 * (6 + ε))) with hc_def
  have hc : 0 < c := lt_min (by positivity) (by positivity)
  have hc1 : c < ε ^ 2 / 64 := by
    have := min_le_left (ε ^ 2 / 128) (ε / (2 * (6 + ε)))
    have : 0 < ε ^ 2 := by positivity
    linarith
  have hc2 : c < ε / (6 + ε) := by
    have := min_le_right (ε ^ 2 / 128) (ε / (2 * (6 + ε)))
    have h6 : ε / (2 * (6 + ε)) < ε / (6 + ε) :=
      div_lt_div_of_pos_left hε (by positivity) (by linarith)
    linarith
  have ev : ∀ᶠ n in atTop, (a n / A a n < ε / (6 + ε) ∧
      a n * Real.log (Real.log (A a n)) / A a n < ε ^ 2 / 64) ∧
      2 * (3 + ε) / (6 + ε) < A a n ∧ 0 < A a n := by
    have e1 := h49.def hc
    have e2 := hLL.eventually_ge_atTop 1
    have e3 := hAt.eventually_gt_atTop (2 * (3 + ε) / (6 + ε))
    have e4 := hAt.eventually_gt_atTop 0
    filter_upwards [e1, e2, e3, e4] with n h1 h2 h3 h4
    refine ⟨?_, h3, h4⟩
    set L := Real.log (Real.log (A a n))
    have hL : 0 < L := by linarith
    have hb : a n / A a n ≤ c / L := by
      have := (le_abs_self _).trans h1
      rw [Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < 1 / L)] at this
      calc a n / A a n ≤ c * (1 / L) := this
        _ = c / L := by ring
    have hb2 : a n / A a n ≤ c := hb.trans (div_le_self hc.le (by linarith))
    refine ⟨by linarith, ?_⟩
    have : a n * L / A a n = (a n / A a n) * L := by ring
    rw [this]
    have : (a n / A a n) * L ≤ c := by
      calc (a n / A a n) * L ≤ (c / L) * L := mul_le_mul_of_nonneg_right hb hL.le
        _ = c := by field_simp
    linarith
  obtain ⟨N, hN⟩ := eventually_atTop.1 ev
  set n1 := max N 1 with hn1
  set q : ℝ := 1 + ε / 3 with hq
  -- step function
  have hex : ∀ m : ℕ, ∃ n : ℕ, q * A a m < A a (n + 1) := by
    intro m
    obtain ⟨n, hn⟩ := (hAt.comp (tendsto_add_atTop_nat 1)).eventually_gt_atTop (q * A a m)
      |>.exists
    exact ⟨n, hn⟩
  classical
  let g : ℕ → ℕ := fun m => Nat.find (hex m)
  have g_spec : ∀ m, q * A a m < A a (g m + 1) := fun m => Nat.find_spec (hex m)
  have g_le : ∀ m, A a (g m) ≤ q * A a m := by
    intro m
    rcases Nat.eq_zero_or_pos (g m) with h0 | hpos
    · rw [h0, BS22e216a2.A_zero]
      have := BS22e216a2.A_nonneg a ha_pos m
      have : 0 ≤ q := by rw [hq]; positivity
      positivity
    · have := Nat.find_min (hex m) (show g m - 1 < g m by omega)
      rw [not_lt, show g m - 1 + 1 = g m by omega] at this
      exact this
  have g_gt : ∀ m, n1 ≤ m → m < g m := by
    intro m hm
    by_contra hcon
    rw [not_lt] at hcon
    have hs := g_spec m
    have h1 := BS22e216a2.A_mono a ha_pos (show g m + 1 ≤ m + 1 by omega)
    have hk := (hN (m + 1) (by omega)).1.1
    have hpos : 0 < A a (m + 1) := (hN (m + 1) (by omega)).2.2
    rw [div_lt_div_iff₀ hpos (by positivity)] at hk
    have hA1 := BS22e216a2.A_succ a m
    rw [hA1] at hk
    have h0 := BS22e216a2.A_nonneg a ha_pos m
    have hqA : q * A a m = A a m + ε / 3 * A a m := by rw [hq]; ring
    have hεA : 0 ≤ ε * A a m := mul_nonneg hε.le h0
    nlinarith
  let nk : ℕ → ℕ := fun k => g^[k - 1] n1
  have nk_ge : ∀ j, n1 ≤ g^[j] n1 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact ih.trans (g_gt _ ih).le
  have nk_succ : ∀ k, 1 ≤ k → nk (k + 1) = g (nk k) := by
    intro k hk
    show g^[k + 1 - 1] n1 = g (g^[k - 1] n1)
    rw [show k + 1 - 1 = (k - 1) + 1 by omega, Function.iterate_succ_apply']
  have nk1 : nk 1 = n1 := by simp [nk]
  refine ⟨nk, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    refine ⟨le_trans (le_max_right N 1) (nk_ge _), ?_⟩
    rw [nk_succ k hk]
    exact g_gt _ (nk_ge _)
  · rw [nk1]; exact (hN n1 (le_max_left N 1)).2.1
  · intro n hn
    rw [nk1] at hn
    exact (hN n (by omega)).1.1
  · intro n hn
    rw [nk1] at hn
    exact (hN n (by omega)).1.2
  · intro k hk
    have e : nk k = g (nk (k - 1)) := by
      have := nk_succ (k - 1) (by omega)
      rwa [show k - 1 + 1 = k by omega] at this
    rw [e]
    have hge : n1 ≤ nk (k - 1) := nk_ge _
    exact ⟨BS22e216a2.A_strict a ha_pos (g_gt _ hge), g_le _, g_spec _⟩
