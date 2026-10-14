-- Prove2me | solution 1 for AzumaWeightedSums.StrongLaw.theorem3_strong_law
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:38:56.908207+00:00
-- url     : https://prove2.me/submissions/b1ef59f8-d153-416f-94d4-12382e4f41bd

import Mathlib
import Definitions.Def_AzumaWeightedSums_IteratedLog_ClassG
import Definitions.Def_AzumaWeightedSums_StrongLaw_ReversedSum

set_option autoImplicit false


-- block_growth (9817455d, proved)
namespace BG9817455d

open AzumaWeightedSums.StrongLaw

theorem A_succ (a : ℕ → ℝ) (n : ℕ) : A a (n + 1) = A a n + a (n + 1) := by
  unfold A
  rw [Finset.sum_Icc_succ_top (by omega)]

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

theorem A_pos (a : ℕ → ℝ) (ha_pos : ∀ n : ℕ, 1 ≤ n → 0 < a n) {n : ℕ} (h : 1 ≤ n) :
    0 < A a n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [A_succ]
  have := A_mono a ha_pos (Nat.zero_le m)
  have h0 : A a 0 = 0 := by simp [A]
  have := ha_pos (m + 1) (by omega)
  linarith

end BG9817455d

open AzumaWeightedSums.StrongLaw in
theorem BG9817455d.sol (a : ℕ → ℝ) (ha_pos : ∀ n : ℕ, 1 ≤ n → 0 < a n)
    (ε : ℝ) (hε : 0 < ε) (nk : ℕ → ℕ)
    (h411 : 2 * (3 + ε) / (6 + ε) < A a (nk 1))
    (h412 : ∀ n : ℕ, nk 1 < n → a n / A a n < ε / (6 + ε))
    (h414 : ∀ k : ℕ, 2 ≤ k →
        A a (nk (k - 1)) < A a (nk k) ∧ A a (nk k) ≤ (1 + ε / 3) * A a (nk (k - 1)) ∧
          (1 + ε / 3) * A a (nk (k - 1)) < A a (nk k + 1)) :
    ∀ k : ℕ, 1 ≤ k → (2 * (3 + ε) / (6 + ε)) ^ (k - 1) < A a (nk k) := by
  have hmono : ∀ k : ℕ, 1 ≤ k → nk 1 ≤ nk k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact le_rfl
    | succ k hk ih =>
      have h := (h414 (k + 1) (by omega)).1
      simp only [Nat.add_sub_cancel] at h
      have : nk k ≤ nk (k + 1) := by
        by_contra hc
        rw [not_le] at hc
        have := BG9817455d.A_mono a ha_pos hc.le
        linarith
      omega
  have hc : 0 < 2 * (3 + ε) / (6 + ε) := by positivity
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    have h1 : (1 : ℝ) < 2 * (3 + ε) / (6 + ε) := by
      rw [lt_div_iff₀ (by positivity)]; linarith
    simp only [Nat.sub_self, pow_zero]
    linarith
  | succ k hk ih =>
    obtain ⟨_, _, h3⟩ := h414 (k + 1) (by omega)
    simp only [Nat.add_sub_cancel] at h3 ⊢
    set n := nk (k + 1) + 1 with hn
    have hnpos : 0 < A a n := BG9817455d.A_pos a ha_pos (by omega)
    have h4 := h412 n (by have := hmono (k + 1) (by omega); omega)
    rw [div_lt_div_iff₀ hnpos (by positivity)] at h4
    have hAn : A a n = A a (nk (k + 1)) + a n := BG9817455d.A_succ a _
    rw [hAn] at h4 h3
    set X := A a (nk (k + 1))
    set Y := A a (nk k)
    have h5 : 6 * a n < ε * X := by nlinarith
    have h6 : (6 + 2 * ε) * Y < (6 + ε) * X := by nlinarith
    have h7 : Y * (2 * (3 + ε) / (6 + ε)) < X := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith
    have hk' : k = (k - 1) + 1 := by omega
    rw [hk', pow_succ]
    calc (2 * (3 + ε) / (6 + ε)) ^ (k - 1) * (2 * (3 + ε) / (6 + ε))
        < Y * (2 * (3 + ε) / (6 + ε)) := mul_lt_mul_of_pos_right ih hc
      _ < X := h7

-- block_sequence_exists (22e216a2, proved)
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
theorem BS22e216a2.sol (a : ℕ → ℝ) (ha_pos : ∀ n : ℕ, 1 ≤ n → 0 < a n)
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

-- tail_le_exp (2eebcb0a, proved)
namespace AzumaTailAux2eeb

open MeasureTheory ProbabilityTheory

lemma exp_mul_le_cosh_add {s x : ℝ} (hx : |x| ≤ 1) :
    Real.exp (s * x) ≤ Real.cosh s + x * Real.sinh s := by
  have h1 : -1 ≤ x := by linarith [neg_abs_le x]
  have h2 : x ≤ 1 := by linarith [le_abs_self x]
  have ha : 0 ≤ (1 + x) / 2 := by linarith
  have hb : 0 ≤ (1 - x) / 2 := by linarith
  have hab : (1 + x) / 2 + (1 - x) / 2 = 1 := by ring
  have := convexOn_exp.2 (Set.mem_univ s) (Set.mem_univ (-s)) ha hb hab
  simp only [smul_eq_mul] at this
  rw [show (1 + x) / 2 * s + (1 - x) / 2 * -s = s * x by ring] at this
  rw [Real.cosh_eq, Real.sinh_eq]
  linear_combination this

lemma norm_exp_le {t S B : ℝ} (h : |S| ≤ B) :
    ‖Real.exp (t * S)‖ ≤ Real.exp (|t| * B) := by
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
  exact (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left h (abs_nonneg t))

theorem mgf_step {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (x : ℕ → Ω → ℝ)
    (hx : AzumaWeightedSums.IteratedLog.IsMartingaleDiff μ ℱ x)
    (hbd : ∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂μ, |x n ω| ≤ 1) (c : ℕ → ℝ) (t : ℝ) (n : ℕ) :
    StronglyMeasurable[ℱ n] (fun ω => ∑ j ∈ Finset.Icc 1 n, c j * x j ω) ∧
      (∀ᵐ ω ∂μ, |∑ j ∈ Finset.Icc 1 n, c j * x j ω| ≤ ∑ j ∈ Finset.Icc 1 n, |c j|) ∧
      ∫ ω, Real.exp (t * ∑ j ∈ Finset.Icc 1 n, c j * x j ω) ∂μ
        ≤ Real.exp ((∑ j ∈ Finset.Icc 1 n, c j ^ 2) * t ^ 2 / 2) := by
  induction n with
  | zero =>
    simp only [Finset.Icc_eq_empty_of_lt, zero_lt_one,
      Finset.sum_empty]
    refine ⟨stronglyMeasurable_const, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨hm, hb, hi⟩ := ih
    have hsplit : ∀ ω, ∑ j ∈ Finset.Icc 1 (n+1), c j * x j ω
        = (∑ j ∈ Finset.Icc 1 n, c j * x j ω) + c (n+1) * x (n+1) ω :=
      fun ω => Finset.sum_Icc_succ_top (by omega) _
    have hsplit2 : ∑ j ∈ Finset.Icc 1 (n+1), c j ^ 2
        = ∑ j ∈ Finset.Icc 1 n, c j ^ 2 + c (n+1) ^ 2 := Finset.sum_Icc_succ_top (by omega) _
    have hsplit3 : ∑ j ∈ Finset.Icc 1 (n+1), |c j|
        = ∑ j ∈ Finset.Icc 1 n, |c j| + |c (n+1)| := Finset.sum_Icc_succ_top (by omega) _
    obtain ⟨hxm, hxi, hxc⟩ := hx (n+1) (by omega)
    simp only [Nat.add_sub_cancel] at hxc
    have hxb := hbd (n+1) (by omega)
    set S : Ω → ℝ := fun ω => ∑ j ∈ Finset.Icc 1 n, c j * x j ω with hS
    set B := ∑ j ∈ Finset.Icc 1 n, |c j| with hB
    refine ⟨?_, ?_, ?_⟩
    · have : (fun ω => ∑ j ∈ Finset.Icc 1 (n+1), c j * x j ω)
          = fun ω => S ω + c (n+1) * x (n+1) ω := funext hsplit
      rw [this]
      exact (hm.mono (ℱ.mono (Nat.le_succ n))).add (hxm.const_mul _)
    · filter_upwards [hb, hxb] with ω h1 h2
      rw [hsplit, hsplit3]
      calc |S ω + c (n+1) * x (n+1) ω| ≤ |S ω| + |c (n+1) * x (n+1) ω| := abs_add_le _ _
        _ ≤ B + |c (n+1)| := add_le_add h1
            (by rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) h2)
    · have hfm : StronglyMeasurable[ℱ n] (fun ω => Real.exp (t * S ω)) :=
        Real.continuous_exp.comp_stronglyMeasurable (hm.const_mul t)
      have hfb : ∀ᵐ ω ∂μ, ‖Real.exp (t * S ω)‖ ≤ Real.exp (|t| * B) := by
        filter_upwards [hb] with ω h1 using norm_exp_le h1
      have hfi : Integrable (fun ω => Real.exp (t * S ω)) μ :=
        Integrable.of_bound (hfm.mono (ℱ.le n)).aestronglyMeasurable _ hfb
      have hxm0 : StronglyMeasurable (x (n+1)) := hxm.mono (ℱ.le (n+1))
      set s := t * c (n+1) with hs
      have hg1 : Integrable (fun ω => Real.exp (t * S ω) * Real.exp (s * x (n+1) ω)) μ := by
        refine Integrable.of_bound ((hfm.mono (ℱ.le n)).aestronglyMeasurable.mul
          (Real.continuous_exp.comp_stronglyMeasurable (hxm0.const_mul s)).aestronglyMeasurable)
          (Real.exp (|t| * B) * Real.exp (|s| * 1)) ?_
        filter_upwards [hfb, hxb] with ω h1 h2
        rw [norm_mul]
        exact mul_le_mul h1 (norm_exp_le h2) (norm_nonneg _) (Real.exp_pos _).le
      have hfx : Integrable (fun ω => Real.exp (t * S ω) * x (n+1) ω) μ := by
        refine Integrable.of_bound ((hfm.mono (ℱ.le n)).aestronglyMeasurable.mul
          hxm0.aestronglyMeasurable) (Real.exp (|t| * B) * 1) ?_
        filter_upwards [hfb, hxb] with ω h1 h2
        rw [norm_mul, Real.norm_eq_abs (x (n+1) ω)]
        exact mul_le_mul h1 h2 (abs_nonneg _) (Real.exp_pos _).le
      have h0 : ∫ ω, Real.exp (t * S ω) * x (n+1) ω ∂μ = 0 := by
        have h := condExp_stronglyMeasurable_mul_of_bound (ℱ.le n) hfm hxi _ hfb
        calc ∫ ω, Real.exp (t * S ω) * x (n+1) ω ∂μ
            = ∫ ω, (μ[(fun ω => Real.exp (t * S ω)) * x (n+1) | ℱ n]) ω ∂μ :=
              (integral_condExp (ℱ.le n)).symm
          _ = ∫ ω, (0:ℝ) ∂μ := by
              refine integral_congr_ae (h.trans ?_)
              filter_upwards [hxc] with ω hω
              simp [Pi.mul_apply, hω]
          _ = 0 := by simp
      have heq : (fun ω => Real.exp (t * ∑ j ∈ Finset.Icc 1 (n+1), c j * x j ω))
          = fun ω => Real.exp (t * S ω) * Real.exp (s * x (n+1) ω) := by
        funext ω
        rw [hsplit, ← Real.exp_add]
        congr 1
        rw [hs]; ring
      rw [heq]
      calc ∫ ω, Real.exp (t * S ω) * Real.exp (s * x (n+1) ω) ∂μ
          ≤ ∫ ω, Real.exp (t * S ω) * (Real.cosh s + x (n+1) ω * Real.sinh s) ∂μ := by
            refine integral_mono_ae hg1 ?_ ?_
            · have : (fun ω => Real.exp (t * S ω) * (Real.cosh s + x (n+1) ω * Real.sinh s))
                  = fun ω => Real.cosh s * Real.exp (t * S ω)
                    + Real.sinh s * (Real.exp (t * S ω) * x (n+1) ω) := by
                funext ω; ring
              rw [this]
              exact (hfi.const_mul _).add (hfx.const_mul _)
            · filter_upwards [hxb] with ω h2
              exact mul_le_mul_of_nonneg_left (exp_mul_le_cosh_add h2) (Real.exp_pos _).le
        _ = Real.cosh s * ∫ ω, Real.exp (t * S ω) ∂μ := by
            have : (fun ω => Real.exp (t * S ω) * (Real.cosh s + x (n+1) ω * Real.sinh s))
                = fun ω => Real.cosh s * Real.exp (t * S ω)
                  + Real.sinh s * (Real.exp (t * S ω) * x (n+1) ω) := by
              funext ω; ring
            rw [this, integral_add (hfi.const_mul _) (hfx.const_mul _), integral_const_mul,
              integral_const_mul, h0]
            ring
        _ ≤ Real.exp (s ^ 2 / 2) * Real.exp ((∑ j ∈ Finset.Icc 1 n, c j ^ 2) * t ^ 2 / 2) :=
            mul_le_mul (Real.cosh_le_exp_half_sq s) hi
              (integral_nonneg (fun _ => (Real.exp_pos _).le)) (Real.exp_pos _).le
        _ = Real.exp ((∑ j ∈ Finset.Icc 1 (n+1), c j ^ 2) * t ^ 2 / 2) := by
            rw [← Real.exp_add, hsplit2, hs]
            congr 1
            ring

end AzumaTailAux2eeb

open MeasureTheory in
theorem AzumaTailAux2eeb.sol {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (x : ℕ → Ω → ℝ)
    (hx : AzumaWeightedSums.IteratedLog.IsMartingaleDiff μ ℱ x) (hbd : ∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂μ, |x n ω| ≤ 1)
    (N : ℕ) (c : ℕ → ℝ) (hc : 0 < ∑ j ∈ Finset.Icc 1 N, c j ^ 2)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    μ.real {ω | lam < ∑ j ∈ Finset.Icc 1 N, c j * x j ω}
      ≤ Real.exp (-lam ^ 2 / (2 * ∑ j ∈ Finset.Icc 1 N, c j ^ 2)) := by
  let cV : NNReal := ⟨∑ j ∈ Finset.Icc 1 N, c j ^ 2, hc.le⟩
  have hsub : ProbabilityTheory.HasSubgaussianMGF
      (fun ω => ∑ j ∈ Finset.Icc 1 N, c j * x j ω) cV μ := by
    refine ⟨fun t => ?_, fun t => ?_⟩
    · obtain ⟨h1, h2, -⟩ := AzumaTailAux2eeb.mgf_step ℱ x hx hbd c t N
      refine Integrable.of_bound
        (Real.continuous_exp.comp_stronglyMeasurable
          ((h1.mono (ℱ.le N)).const_mul t)).aestronglyMeasurable
        (Real.exp (|t| * ∑ j ∈ Finset.Icc 1 N, |c j|)) ?_
      filter_upwards [h2] with ω h using AzumaTailAux2eeb.norm_exp_le h
    · obtain ⟨-, -, h3⟩ := AzumaTailAux2eeb.mgf_step ℱ x hx hbd c t N
      exact h3
  calc μ.real {ω | lam < ∑ j ∈ Finset.Icc 1 N, c j * x j ω}
      ≤ μ.real {ω | lam ≤ ∑ j ∈ Finset.Icc 1 N, c j * x j ω} :=
        measureReal_mono (fun ω (h : lam < _) => show lam ≤ _ from le_of_lt h)
    _ ≤ Real.exp (-lam ^ 2 / (2 * cV)) := hsub.measure_ge_le hlam
    _ = Real.exp (-lam ^ 2 / (2 * ∑ j ∈ Finset.Icc 1 N, c j ^ 2)) := rfl

-- eq_4_15_maximal (b1982cee, proved 10-13)
namespace K2b1982cee

open MeasureTheory AzumaWeightedSums.StrongLaw

/-- Orthogonality: a bounded `ℱ (l-1)`-measurable `g` is orthogonal to the martingale difference `x l`. -/
theorem orth {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (x : ℕ → Ω → ℝ)
    (hx : AzumaWeightedSums.IteratedLog.IsMartingaleDiff μ ℱ x) (l : ℕ) (hl : 1 ≤ l)
    (g : Ω → ℝ) (hg : StronglyMeasurable[ℱ (l - 1)] g) (C : ℝ) (hgb : ∀ᵐ ω ∂μ, |g ω| ≤ C) :
    Integrable (fun ω => g ω * x l ω) μ ∧ ∫ ω, g ω * x l ω ∂μ = 0 := by
  obtain ⟨-, hxi, hce⟩ := hx l hl
  have hgm : AEStronglyMeasurable g μ := (hg.mono (ℱ.le (l - 1))).aestronglyMeasurable
  have hint : Integrable (fun ω => g ω * x l ω) μ :=
    hxi.bdd_mul hgm (c := C) (by filter_upwards [hgb] with ω h; simpa [Real.norm_eq_abs] using h)
  refine ⟨hint, ?_⟩
  rw [← integral_condExp (ℱ.le (l - 1))]
  have h1 : μ[(fun ω => g ω * x l ω) | ℱ (l - 1)] =ᵐ[μ] fun ω => g ω * μ[x l | ℱ (l - 1)] ω :=
    condExp_mul_of_stronglyMeasurable_left hg hint hxi
  rw [integral_congr_ae h1]
  have h2 : (fun ω => g ω * μ[x l | ℱ (l - 1)] ω) =ᵐ[μ] fun _ => (0 : ℝ) := by
    filter_upwards [hce] with ω h
    simp [h]
  rw [integral_congr_ae h2]
  simp

theorem hall {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} (x : ℕ → Ω → ℝ)
    (hbd : ∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂μ, |x n ω| ≤ 1) :
    ∀ᵐ ω ∂μ, ∀ j : ℕ, 1 ≤ j → |x j ω| ≤ 1 := by
  rw [ae_all_iff]
  intro j
  by_cases hj : 1 ≤ j
  · filter_upwards [hbd j hj] with ω h _ using h
  · exact Filter.Eventually.of_forall (fun ω h => absurd h hj)

/-- One step of the second-moment recursion. -/
theorem step {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (x : ℕ → Ω → ℝ)
    (hx : AzumaWeightedSums.IteratedLog.IsMartingaleDiff μ ℱ x)
    (hbd : ∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂μ, |x n ω| ≤ 1)
    (N : ℕ) (B : Set Ω) (hB : MeasurableSet[ℱ N] B) (t c C : ℝ) (Y : Ω → ℝ)
    (hYm : StronglyMeasurable[ℱ N] Y) (hYb : ∀ᵐ ω ∂μ, |Y ω| ≤ C) :
    Integrable (B.indicator (fun ω => (t - Y ω) ^ 2)) μ ∧
    Integrable (B.indicator (fun ω => (t - (Y ω + c * x (N + 1) ω)) ^ 2)) μ ∧
    ∫ ω, B.indicator (fun ω => (t - (Y ω + c * x (N + 1) ω)) ^ 2) ω ∂μ
      ≤ ∫ ω, B.indicator (fun ω => (t - Y ω) ^ 2) ω ∂μ + c ^ 2 * μ.real B := by
  have hBm : MeasurableSet B := ℱ.le N B hB
  have hYm0 : StronglyMeasurable Y := hYm.mono (ℱ.le N)
  have hx1 : StronglyMeasurable (x (N + 1)) := ((hx (N + 1) (by omega)).1).mono (ℱ.le (N + 1))
  have hxb := hbd (N + 1) (by omega)
  have i1 : Integrable (B.indicator (fun ω => (t - Y ω) ^ 2)) μ := by
    refine Integrable.of_bound
      (((stronglyMeasurable_const.sub hYm0).pow 2).indicator hBm).aestronglyMeasurable
      ((|t| + C) ^ 2) ?_
    filter_upwards [hYb] with ω hω
    rw [Real.norm_eq_abs]
    by_cases hωB : ω ∈ B
    · rw [Set.indicator_of_mem hωB, abs_pow]
      have : |t - Y ω| ≤ |t| + C := (abs_sub _ _).trans (by linarith)
      exact pow_le_pow_left₀ (abs_nonneg _) this 2
    · rw [Set.indicator_of_notMem hωB, abs_zero]
      positivity
  set g : Ω → ℝ := B.indicator (fun ω => -2 * c * (t - Y ω)) with hgdef
  have hgm : StronglyMeasurable[ℱ (N + 1 - 1)] g := by
    rw [Nat.add_sub_cancel]
    exact ((stronglyMeasurable_const.sub hYm).const_mul (-2 * c)).indicator hB
  have hgb : ∀ᵐ ω ∂μ, |g ω| ≤ 2 * |c| * (|t| + C) := by
    filter_upwards [hYb] with ω hω
    have hC : 0 ≤ C := (abs_nonneg _).trans hω
    by_cases hωB : ω ∈ B
    · rw [hgdef, Set.indicator_of_mem hωB, abs_mul, abs_mul]
      have h2 : |(-2 : ℝ)| = 2 := by norm_num
      rw [h2]
      have : |t - Y ω| ≤ |t| + C := (abs_sub _ _).trans (by linarith)
      have hc : 0 ≤ 2 * |c| := by positivity
      calc 2 * |c| * |t - Y ω| ≤ 2 * |c| * (|t| + C) := mul_le_mul_of_nonneg_left this hc
        _ = 2 * |c| * (|t| + C) := rfl
    · rw [hgdef, Set.indicator_of_notMem hωB, abs_zero]
      positivity
  obtain ⟨hgi, hg0⟩ := orth ℱ x hx (N + 1) (by omega) g hgm _ hgb
  set h3 : Ω → ℝ := B.indicator (fun ω => c ^ 2 * x (N + 1) ω ^ 2) with hh3
  have h3b : ∀ᵐ ω ∂μ, h3 ω ≤ B.indicator (fun _ => c ^ 2) ω ∧ 0 ≤ h3 ω := by
    filter_upwards [hxb] with ω hω
    have hx2 : x (N + 1) ω ^ 2 ≤ 1 := by
      rw [← sq_abs]; nlinarith [abs_nonneg (x (N + 1) ω)]
    by_cases hωB : ω ∈ B
    · rw [hh3, Set.indicator_of_mem hωB, Set.indicator_of_mem hωB]
      constructor
      · nlinarith [sq_nonneg c]
      · positivity
    · rw [hh3, Set.indicator_of_notMem hωB, Set.indicator_of_notMem hωB]
      exact ⟨le_rfl, le_rfl⟩
  have h3i : Integrable h3 μ := by
    refine Integrable.of_bound
      ((stronglyMeasurable_const.mul (hx1.pow 2)).indicator hBm).aestronglyMeasurable (c ^ 2) ?_
    filter_upwards [h3b] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg hω.2]
    refine hω.1.trans ?_
    by_cases hωB : ω ∈ B
    · rw [Set.indicator_of_mem hωB]
    · rw [Set.indicator_of_notMem hωB]; positivity
  have hsplit : B.indicator (fun ω => (t - (Y ω + c * x (N + 1) ω)) ^ 2)
      = fun ω => B.indicator (fun ω => (t - Y ω) ^ 2) ω + g ω * x (N + 1) ω + h3 ω := by
    funext ω
    by_cases hωB : ω ∈ B
    · rw [hgdef, hh3, Set.indicator_of_mem hωB, Set.indicator_of_mem hωB,
        Set.indicator_of_mem hωB, Set.indicator_of_mem hωB]
      ring
    · rw [hgdef, hh3, Set.indicator_of_notMem hωB, Set.indicator_of_notMem hωB,
        Set.indicator_of_notMem hωB, Set.indicator_of_notMem hωB]
      ring
  refine ⟨i1, ?_, ?_⟩
  · rw [hsplit]; exact (i1.add hgi).add h3i
  · rw [hsplit]
    have e1 := integral_add (i1.add hgi) h3i
    have e2 := integral_add i1 hgi
    simp only [Pi.add_apply] at e1 e2
    show ∫ ω, (B.indicator (fun ω => (t - Y ω) ^ 2) ω + g ω * x (N + 1) ω + h3 ω) ∂μ ≤ _
    rw [e1, e2, hg0]
    have h3le : ∫ ω, h3 ω ∂μ ≤ c ^ 2 * μ.real B := by
      have e : ∫ ω, B.indicator (fun _ => c ^ 2) ω ∂μ = μ.real B • c ^ 2 :=
        integral_indicator_const _ hBm
      rw [smul_eq_mul] at e
      rw [mul_comm, ← e]
      exact integral_mono_ae h3i ((integrable_const _).indicator hBm) (h3b.mono fun ω h => h.1)
    linarith

/-- Second moment of `t - Y` on an `ℱ n`-event. -/
theorem moment {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (x : ℕ → Ω → ℝ)
    (hx : AzumaWeightedSums.IteratedLog.IsMartingaleDiff μ ℱ x)
    (hbd : ∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂μ, |x n ω| ≤ 1)
    (n : ℕ) (c : ℕ → ℝ) (B : Set Ω) (hB : MeasurableSet[ℱ n] B) (t : ℝ) (N : ℕ) :
    Integrable (B.indicator (fun ω => (t - ∑ j ∈ Finset.Ioc n N, c j * x j ω) ^ 2)) μ ∧
    ∫ ω, B.indicator (fun ω => (t - ∑ j ∈ Finset.Ioc n N, c j * x j ω) ^ 2) ω ∂μ
      ≤ (t ^ 2 + ∑ j ∈ Finset.Ioc n N, c j ^ 2) * μ.real B := by
  have hBm : MeasurableSet B := ℱ.le n B hB
  have hall' := hall x hbd
  have hempty : ∀ N : ℕ, N ≤ n →
      (Integrable (B.indicator (fun ω => (t - ∑ j ∈ Finset.Ioc n N, c j * x j ω) ^ 2)) μ ∧
      ∫ ω, B.indicator (fun ω => (t - ∑ j ∈ Finset.Ioc n N, c j * x j ω) ^ 2) ω ∂μ
        ≤ (t ^ 2 + ∑ j ∈ Finset.Ioc n N, c j ^ 2) * μ.real B) := by
    intro N hN
    have he : Finset.Ioc n N = ∅ := Finset.Ioc_eq_empty (by omega)
    simp only [he, Finset.sum_empty, sub_zero, add_zero]
    refine ⟨(integrable_const _).indicator hBm, ?_⟩
    rw [integral_indicator_const _ hBm, smul_eq_mul, mul_comm]
  induction N with
  | zero => exact hempty 0 (Nat.zero_le _)
  | succ N ih =>
    by_cases hnN : n ≤ N
    swap
    · exact hempty (N + 1) (by omega)
    have hYm : StronglyMeasurable[ℱ N] (fun ω => ∑ j ∈ Finset.Ioc n N, c j * x j ω) := by
      apply Finset.stronglyMeasurable_fun_sum
      intro j hj
      simp only [Finset.mem_Ioc] at hj
      exact (((hx j (by omega)).1).mono (ℱ.mono hj.2)).const_mul (c j)
    have hYb : ∀ᵐ ω ∂μ, |∑ j ∈ Finset.Ioc n N, c j * x j ω| ≤ ∑ j ∈ Finset.Ioc n N, |c j| := by
      filter_upwards [hall'] with ω hω
      calc |∑ j ∈ Finset.Ioc n N, c j * x j ω| ≤ ∑ j ∈ Finset.Ioc n N, |c j * x j ω| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j ∈ Finset.Ioc n N, |c j| := by
          apply Finset.sum_le_sum
          intro j hj
          simp only [Finset.mem_Ioc] at hj
          rw [abs_mul]
          exact mul_le_of_le_one_right (abs_nonneg _) (hω j (by omega))
    obtain ⟨-, i2, hle⟩ := step ℱ x hx hbd N B (ℱ.mono hnN B hB) t (c (N + 1)) _
      (fun ω => ∑ j ∈ Finset.Ioc n N, c j * x j ω) hYm hYb
    simp only [Finset.sum_Ioc_succ_top hnN]
    refine ⟨i2, ?_⟩
    have := ih.2
    nlinarith

/-- Cantelli on an `ℱ n`-event. -/
theorem cantelli {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (x : ℕ → Ω → ℝ)
    (hx : AzumaWeightedSums.IteratedLog.IsMartingaleDiff μ ℱ x)
    (hbd : ∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂μ, |x n ω| ≤ 1)
    (n N : ℕ) (c : ℕ → ℝ) (B D : Set Ω) (hB : MeasurableSet[ℱ n] B) (hD : MeasurableSet D)
    (hDB : D ⊆ B) (t : ℝ) (ht : 0 < t)
    (hσ : ∑ j ∈ Finset.Ioc n N, c j ^ 2 < t ^ 2)
    (hY : ∀ᵐ ω ∂μ, ω ∈ D → ∑ j ∈ Finset.Ioc n N, c j * x j ω ≤ -t) :
    μ.real D ≤ μ.real B / 2 := by
  obtain ⟨hi, hm⟩ := moment ℱ x hx hbd n c B hB t N
  have h1 : ∫ ω, D.indicator (fun _ => 4 * t ^ 2) ω ∂μ
      ≤ ∫ ω, B.indicator (fun ω => (t - ∑ j ∈ Finset.Ioc n N, c j * x j ω) ^ 2) ω ∂μ := by
    apply integral_mono_ae ((integrable_const _).indicator hD) hi
    filter_upwards [hY] with ω hω
    by_cases hωD : ω ∈ D
    · rw [Set.indicator_of_mem hωD, Set.indicator_of_mem (hDB hωD)]
      have hy := hω hωD
      nlinarith
    · rw [Set.indicator_of_notMem hωD]
      exact Set.indicator_nonneg (fun _ _ => sq_nonneg _) _
  rw [integral_indicator_const _ hD, smul_eq_mul] at h1
  have hBnn : 0 ≤ μ.real B := measureReal_nonneg
  have h2 : μ.real D * (4 * t ^ 2) ≤ (2 * t ^ 2) * μ.real B := by nlinarith
  have ht2 : 0 < t ^ 2 := by positivity
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
  nlinarith

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

theorem a_mono' (a : ℕ → ℝ) (ha_mono : ∀ n : ℕ, 1 ≤ n → a n ≤ a (n + 1)) {i k : ℕ}
    (hi : 1 ≤ i) (hik : i ≤ k) : a i ≤ a k := by
  induction k, hik using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih => exact ih.trans (ha_mono k (by omega))

theorem Icc_one (m : ℕ) : Finset.Icc 1 m = Finset.Ioc 0 m := by
  ext j
  simp only [Finset.mem_Icc, Finset.mem_Ioc]
  omega

theorem refl_sum (a : ℕ → ℝ) (m : ℕ) : ∑ j ∈ Finset.Ioc 0 m, a (m + 1 - j) = A a m := by
  unfold A
  rw [Icc_one]
  apply Finset.sum_nbij' (fun j => m + 1 - j) (fun j => m + 1 - j)
  · intro j hj
    simp only [Finset.mem_Ioc, Finset.coe_Ioc, Set.mem_Ioc] at hj ⊢
    omega
  · intro j hj
    simp only [Finset.mem_Ioc, Finset.coe_Ioc, Set.mem_Ioc] at hj ⊢
    omega
  · intro j hj
    simp only [Finset.mem_Ioc, Finset.coe_Ioc, Set.mem_Ioc] at hj
    omega
  · intro j hj
    simp only [Finset.mem_Ioc, Finset.coe_Ioc, Set.mem_Ioc] at hj
    omega
  · intro j _
    rfl

/-- Deterministic split `S̄_{N₁} = S̄_n + F + Y` with `|F| ≤ A_{N₁} − T − A_n`. -/
theorem sbar_split {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} (x : ℕ → Ω → ℝ)
    (hbd : ∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂μ, |x n ω| ≤ 1)
    (a : ℕ → ℝ) (ha_mono : ∀ n : ℕ, 1 ≤ n → a n ≤ a (n + 1)) (n N₁ : ℕ) (hn : n ≤ N₁) :
    ∀ᵐ ω ∂μ, |Sbar a x N₁ ω - Sbar a x n ω - ∑ j ∈ Finset.Ioc n N₁, a (N₁ + 1 - j) * x j ω|
      ≤ A a N₁ - ∑ j ∈ Finset.Ioc n N₁, a (N₁ + 1 - j) - A a n := by
  filter_upwards [hall x hbd] with ω hω
  have e1 : Sbar a x N₁ ω = ∑ j ∈ Finset.Ioc 0 n, a (N₁ + 1 - j) * x j ω
      + ∑ j ∈ Finset.Ioc n N₁, a (N₁ + 1 - j) * x j ω := by
    unfold Sbar
    rw [Icc_one, Finset.sum_Ioc_consecutive _ (Nat.zero_le n) hn]
  have e2 : Sbar a x n ω = ∑ j ∈ Finset.Ioc 0 n, a (n + 1 - j) * x j ω := by
    unfold Sbar
    rw [Icc_one]
  have e3 : A a N₁ = ∑ j ∈ Finset.Ioc 0 n, a (N₁ + 1 - j)
      + ∑ j ∈ Finset.Ioc n N₁, a (N₁ + 1 - j) := by
    rw [← refl_sum, Finset.sum_Ioc_consecutive _ (Nat.zero_le n) hn]
  have e4 : A a n = ∑ j ∈ Finset.Ioc 0 n, a (n + 1 - j) := (refl_sum a n).symm
  have key : |∑ j ∈ Finset.Ioc 0 n, (a (N₁ + 1 - j) - a (n + 1 - j)) * x j ω|
      ≤ ∑ j ∈ Finset.Ioc 0 n, (a (N₁ + 1 - j) - a (n + 1 - j)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
    simp only [Finset.mem_Ioc] at hj
    have hd : 0 ≤ a (N₁ + 1 - j) - a (n + 1 - j) :=
      sub_nonneg.2 (a_mono' a ha_mono (by omega) (by omega))
    rw [abs_mul, abs_of_nonneg hd]
    exact mul_le_of_le_one_right hd (hω j (by omega))
  have eL : Sbar a x N₁ ω - Sbar a x n ω - ∑ j ∈ Finset.Ioc n N₁, a (N₁ + 1 - j) * x j ω
      = ∑ j ∈ Finset.Ioc 0 n, (a (N₁ + 1 - j) - a (n + 1 - j)) * x j ω := by
    rw [e1, e2]
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  have eR : A a N₁ - ∑ j ∈ Finset.Ioc n N₁, a (N₁ + 1 - j) - A a n
      = ∑ j ∈ Finset.Ioc 0 n, (a (N₁ + 1 - j) - a (n + 1 - j)) := by
    rw [e3, e4, Finset.sum_sub_distrib]
    ring
  rw [eL, eR]
  exact key

/-- Display (4.15). -/
theorem main {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (x : ℕ → Ω → ℝ)
    (hx : AzumaWeightedSums.IteratedLog.IsMartingaleDiff μ ℱ x)
    (hbd : ∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂μ, |x n ω| ≤ 1)
    (a : ℕ → ℝ) (ha_pos : ∀ n : ℕ, 1 ≤ n → 0 < a n)
    (ha_mono : ∀ n : ℕ, 1 ≤ n → a n ≤ a (n + 1))
    (ε : ℝ) (hε : 0 < ε) (N₀ N₁ : ℕ) (hN₀ : 1 ≤ N₀) (hN : N₀ < N₁)
    (hA : A a N₁ ≤ (1 + ε / 3) * A a N₀) :
    μ.real {ω | ∃ n ∈ Finset.Ioc N₀ N₁, ε * A a N₀ < Sbar a x n ω}
      ≤ 2 * μ.real {ω | ε / 2 * A a N₀ < Sbar a x N₁ ω} := by
  classical
  have hA0 : 0 < A a N₀ := by
    refine lt_of_lt_of_le (ha_pos 1 le_rfl) ?_
    unfold A
    exact Finset.single_le_sum (f := a) (fun i hi => (ha_pos i (Finset.mem_Icc.1 hi).1).le)
      (Finset.mem_Icc.2 ⟨le_rfl, hN₀⟩)
  have hSm : ∀ m k : ℕ, m ≤ k → StronglyMeasurable[ℱ k] (Sbar a x m) := by
    intro m k hmk
    show StronglyMeasurable[ℱ k] (fun ω => ∑ j ∈ Finset.Icc 1 m, a (m + 1 - j) * x j ω)
    apply Finset.stronglyMeasurable_fun_sum
    intro j hj
    simp only [Finset.mem_Icc] at hj
    exact (((hx j hj.1).1).mono (ℱ.mono (by omega))).const_mul _
  let Bs : ℕ → Set Ω := fun n =>
    {ω | ε * A a N₀ < Sbar a x n ω} ∩ ⋂ m ∈ Finset.Ioo N₀ n, {ω | Sbar a x m ω ≤ ε * A a N₀}
  have hBm : ∀ n, MeasurableSet[ℱ n] (Bs n) := by
    intro n
    show MeasurableSet[ℱ n] ({ω | ε * A a N₀ < Sbar a x n ω}
      ∩ ⋂ m ∈ Finset.Ioo N₀ n, {ω | Sbar a x m ω ≤ ε * A a N₀})
    refine (stronglyMeasurable_const.measurableSet_lt (hSm n n le_rfl)).inter ?_
    refine Finset.measurableSet_biInter _ (fun m hm => ?_)
    simp only [Finset.mem_Ioo] at hm
    exact (hSm m n hm.2.le).measurableSet_le stronglyMeasurable_const
  have hBm0 : ∀ n, MeasurableSet (Bs n) := fun n => ℱ.le n _ (hBm n)
  set G : Set Ω := {ω | ε / 2 * A a N₀ < Sbar a x N₁ ω} with hG
  have hGm : MeasurableSet G :=
    stronglyMeasurable_const.measurableSet_lt ((hSm N₁ N₁ le_rfl).mono (ℱ.le N₁))
  have hsub : {ω | ∃ n ∈ Finset.Ioc N₀ N₁, ε * A a N₀ < Sbar a x n ω}
      ⊆ ⋃ n ∈ Finset.Ioc N₀ N₁, Bs n := by
    rintro ω ⟨n, hn, hlt⟩
    set s := (Finset.Ioc N₀ N₁).filter (fun k => ε * A a N₀ < Sbar a x k ω) with hs
    have hne : s.Nonempty := ⟨n, Finset.mem_filter.2 ⟨hn, hlt⟩⟩
    have hmin : s.min' hne ∈ Finset.Ioc N₀ N₁ ∧ ε * A a N₀ < Sbar a x (s.min' hne) ω :=
      Finset.mem_filter.1 (Finset.min'_mem s hne)
    refine Set.mem_iUnion₂.2 ⟨s.min' hne, hmin.1, hmin.2, ?_⟩
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    intro m hm
    by_contra hc
    rw [not_le] at hc
    simp only [Finset.mem_Ioo] at hm
    have hmax := (Finset.mem_Ioc.1 hmin.1).2
    have hms : m ∈ s := Finset.mem_filter.2 ⟨Finset.mem_Ioc.2 ⟨hm.1, by omega⟩, hc⟩
    have := Finset.min'_le s m hms
    omega
  have hstep : ∀ n ∈ Finset.Ioc N₀ N₁, μ.real (Bs n) ≤ 2 * μ.real (Bs n ∩ G) := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hcpos : ∀ j ∈ Finset.Ioc n N₁, 0 ≤ a (N₁ + 1 - j) := by
      intro j hj
      simp only [Finset.mem_Ioc] at hj
      exact (ha_pos _ (by omega)).le
    set T := ∑ j ∈ Finset.Ioc n N₁, a (N₁ + 1 - j) with hT
    have hT0 : 0 ≤ T := Finset.sum_nonneg hcpos
    have hεA : 0 < ε * A a N₀ := mul_pos hε hA0
    set t := ε * A a N₀ / 6 + T with ht
    have htpos : 0 < t := by linarith
    have hσ : ∑ j ∈ Finset.Ioc n N₁, (fun j => a (N₁ + 1 - j)) j ^ 2 < t ^ 2 := by
      have h1 : ∑ j ∈ Finset.Ioc n N₁, a (N₁ + 1 - j) ^ 2 ≤ T ^ 2 := by
        rw [sq T, hT, Finset.sum_mul]
        apply Finset.sum_le_sum
        intro j hj
        rw [sq]
        exact mul_le_mul_of_nonneg_left (Finset.single_le_sum hcpos hj) (hcpos j hj)
      have h2 : T ^ 2 < t ^ 2 := by nlinarith
      simp only
      linarith
    have hAn : A a N₀ ≤ A a n := A_mono a ha_pos hn.1.le
    have hY : ∀ᵐ ω ∂μ, ω ∈ Bs n \ G →
        ∑ j ∈ Finset.Ioc n N₁, (fun j => a (N₁ + 1 - j)) j * x j ω ≤ -t := by
      filter_upwards [sbar_split x hbd a ha_mono n N₁ hn.2] with ω hω hωD
      obtain ⟨⟨h1, -⟩, h2⟩ := hωD
      simp only [Set.mem_setOf_eq] at h1
      simp only [hG, Set.mem_setOf_eq, not_lt] at h2
      have h3 := (abs_le.1 hω).1
      linarith
    have hD : MeasurableSet (Bs n \ G) := (hBm0 n).diff hGm
    have hc := cantelli ℱ x hx hbd n N₁ (fun j => a (N₁ + 1 - j)) (Bs n) (Bs n \ G) (hBm n) hD
      Set.diff_subset t htpos hσ hY
    have hu : μ.real (Bs n) ≤ μ.real (Bs n ∩ G) + μ.real (Bs n \ G) := by
      calc μ.real (Bs n) = μ.real ((Bs n ∩ G) ∪ (Bs n \ G)) := by rw [Set.inter_union_diff]
        _ ≤ _ := measureReal_union_le _ _
    linarith
  have hdisj : Set.PairwiseDisjoint (↑(Finset.Ioc N₀ N₁)) (fun n => Bs n ∩ G) := by
    intro i hi j hj hij
    simp only [Finset.coe_Ioc, Set.mem_Ioc] at hi hj
    rw [Function.onFun, Set.disjoint_left]
    rintro ω ⟨⟨hi1, hi2⟩, -⟩ ⟨⟨hj1, hj2⟩, -⟩
    simp only [Set.mem_setOf_eq, Set.mem_iInter] at hi1 hi2 hj1 hj2
    rcases lt_or_gt_of_ne hij with h | h
    · have := hj2 i (Finset.mem_Ioo.2 ⟨hi.1, h⟩)
      linarith
    · have := hi2 j (Finset.mem_Ioo.2 ⟨hj.1, h⟩)
      linarith
  have hsum : ∑ n ∈ Finset.Ioc N₀ N₁, μ.real (Bs n ∩ G) ≤ μ.real G := by
    rw [← measureReal_biUnion_finset hdisj (fun n _ => (hBm0 n).inter hGm)]
    exact measureReal_mono (Set.iUnion₂_subset fun n _ => Set.inter_subset_right)
  calc μ.real {ω | ∃ n ∈ Finset.Ioc N₀ N₁, ε * A a N₀ < Sbar a x n ω}
      ≤ μ.real (⋃ n ∈ Finset.Ioc N₀ N₁, Bs n) := measureReal_mono hsub (measure_ne_top μ _)
    _ ≤ ∑ n ∈ Finset.Ioc N₀ N₁, μ.real (Bs n) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ n ∈ Finset.Ioc N₀ N₁, 2 * μ.real (Bs n ∩ G) := Finset.sum_le_sum hstep
    _ = 2 * ∑ n ∈ Finset.Ioc N₀ N₁, μ.real (Bs n ∩ G) := by rw [Finset.mul_sum]
    _ ≤ 2 * μ.real G := by linarith

end K2b1982cee

namespace P0bb8376a

open MeasureTheory AzumaWeightedSums.StrongLaw Filter Topology

theorem nk_ge (nk : ℕ → ℕ) (hnk : ∀ k : ℕ, 1 ≤ k → 1 ≤ nk k ∧ nk k < nk (k + 1)) :
    ∀ k : ℕ, 1 ≤ k → k ≤ nk k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact (hnk 1 le_rfl).1
  | succ k hk ih =>
    have := (hnk k hk).2
    omega

theorem nk_mono (nk : ℕ → ℕ) (hnk : ∀ k : ℕ, 1 ≤ k → 1 ≤ nk k ∧ nk k < nk (k + 1))
    {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) : nk i ≤ nk j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hj ih =>
    have := (hnk j (by omega)).2
    omega

/-- One block: (4.15) followed by the exponential tail bound and (4.13). -/
theorem term_le {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (x : ℕ → Ω → ℝ)
    (hx : AzumaWeightedSums.IteratedLog.IsMartingaleDiff μ ℱ x)
    (hbd : ∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂μ, |x n ω| ≤ 1)
    (a : ℕ → ℝ) (ha_pos : ∀ n : ℕ, 1 ≤ n → 0 < a n)
    (ha_mono : ∀ n : ℕ, 1 ≤ n → a n ≤ a (n + 1))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (N₀ N₁ : ℕ) (hN₀ : 1 ≤ N₀) (hN : N₀ < N₁)
    (hA : A a N₁ ≤ (1 + ε / 3) * A a N₀)
    (h413 : a N₁ * Real.log (Real.log (A a N₁)) / A a N₁ < ε ^ 2 / 64)
    (hL : 1 ≤ Real.log (A a N₁)) :
    μ.real {ω | ∃ n ∈ Finset.Ioc N₀ N₁, ε * A a N₀ < Sbar a x n ω}
      ≤ 2 * (1 / Real.log (A a N₁) ^ 2) := by
  have hK2 := K2b1982cee.main ℱ x hx hbd a ha_pos ha_mono ε hε N₀ N₁ hN₀ hN hA
  have hA0 : 0 < A a N₀ := BG9817455d.A_pos a ha_pos hN₀
  have hA1 : 0 < A a N₁ := BG9817455d.A_pos a ha_pos (by omega)
  have ha1 : 0 < a N₁ := ha_pos N₁ (by omega)
  have hσpos : 0 < ∑ j ∈ Finset.Icc 1 N₁, a (N₁ + 1 - j) ^ 2 := by
    apply Finset.sum_pos
    · intro j hj
      simp only [Finset.mem_Icc] at hj
      exact pow_pos (ha_pos _ (by omega)) 2
    · exact ⟨1, Finset.mem_Icc.2 ⟨le_rfl, by omega⟩⟩
  have hσle : ∑ j ∈ Finset.Icc 1 N₁, a (N₁ + 1 - j) ^ 2 ≤ a N₁ * A a N₁ := by
    rw [← K2b1982cee.refl_sum, Finset.mul_sum, ← K2b1982cee.Icc_one]
    apply Finset.sum_le_sum
    intro j hj
    simp only [Finset.mem_Icc] at hj
    have h1 := ha_pos (N₁ + 1 - j) (by omega)
    have h2 := K2b1982cee.a_mono' a ha_mono (i := N₁ + 1 - j) (k := N₁) (by omega) (by omega)
    nlinarith
  have hlam : 0 ≤ ε / 2 * A a N₀ := by positivity
  have htail : μ.real {ω | ε / 2 * A a N₀ < Sbar a x N₁ ω}
      ≤ Real.exp (-(ε / 2 * A a N₀) ^ 2 / (2 * ∑ j ∈ Finset.Icc 1 N₁, a (N₁ + 1 - j) ^ 2)) :=
    AzumaTailAux2eeb.sol ℱ x hx hbd N₁ (fun j => a (N₁ + 1 - j)) hσpos _ hlam
  have hLpos : 0 < Real.log (A a N₁) := by linarith
  have hLL : 0 ≤ Real.log (Real.log (A a N₁)) := Real.log_nonneg hL
  have hexp : Real.exp (-(ε / 2 * A a N₀) ^ 2 / (2 * ∑ j ∈ Finset.Icc 1 N₁, a (N₁ + 1 - j) ^ 2))
      ≤ 1 / Real.log (A a N₁) ^ 2 := by
    have e : Real.exp (-(2 * Real.log (Real.log (A a N₁)))) = 1 / Real.log (A a N₁) ^ 2 := by
      rw [Real.exp_neg, show 2 * Real.log (Real.log (A a N₁))
          = Real.log (Real.log (A a N₁)) + Real.log (Real.log (A a N₁)) by ring,
        Real.exp_add, Real.exp_log hLpos]
      ring
    rw [← e]
    apply Real.exp_le_exp.2
    rw [neg_div, neg_le_neg_iff, le_div_iff₀ (by positivity)]
    have h1 : a N₁ * Real.log (Real.log (A a N₁)) < ε ^ 2 / 64 * A a N₁ := by
      rwa [div_lt_iff₀ hA1] at h413
    have h2 : A a N₁ ≤ 4 / 3 * A a N₀ := by nlinarith [mul_le_mul_of_nonneg_right hε1 hA0.le]
    have h3 : 2 * Real.log (Real.log (A a N₁)) * (2 * ∑ j ∈ Finset.Icc 1 N₁, a (N₁ + 1 - j) ^ 2)
        ≤ 4 * Real.log (Real.log (A a N₁)) * (a N₁ * A a N₁) := by
      nlinarith [mul_le_mul_of_nonneg_left hσle hLL]
    have h4 : 4 * Real.log (Real.log (A a N₁)) * (a N₁ * A a N₁) ≤ ε ^ 2 / 16 * A a N₁ ^ 2 := by
      nlinarith [mul_lt_mul_of_pos_left h1 hA1]
    have h5 : A a N₁ ^ 2 ≤ 16 / 9 * A a N₀ ^ 2 := by
      nlinarith [mul_le_mul h2 h2 hA1.le (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left h5 (sq_nonneg ε)]
  linarith

theorem summable_blocks {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (x : ℕ → Ω → ℝ)
    (hx : AzumaWeightedSums.IteratedLog.IsMartingaleDiff μ ℱ x)
    (hbd : ∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂μ, |x n ω| ≤ 1)
    (a : ℕ → ℝ) (ha_pos : ∀ n : ℕ, 1 ≤ n → 0 < a n) (ha_mono : ∀ n : ℕ, 1 ≤ n → a n ≤ a (n + 1))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (nk : ℕ → ℕ)
    (hnk : ∀ k : ℕ, 1 ≤ k → 1 ≤ nk k ∧ nk k < nk (k + 1))
    (h411 : 2 * (3 + ε) / (6 + ε) < A a (nk 1))
    (h412 : ∀ n : ℕ, nk 1 < n → a n / A a n < ε / (6 + ε))
    (h413 : ∀ n : ℕ, nk 1 < n → a n * Real.log (Real.log (A a n)) / A a n < ε ^ 2 / 64)
    (h414 : ∀ k : ℕ, 2 ≤ k → A a (nk (k - 1)) < A a (nk k) ∧
        A a (nk k) ≤ (1 + ε / 3) * A a (nk (k - 1)) ∧ (1 + ε / 3) * A a (nk (k - 1)) < A a (nk k + 1)) :
    Summable (fun k : ℕ => μ.real {ω | ∃ n ∈ Finset.Ioc (nk (k + 1)) (nk (k + 2)),
      ε * A a (nk (k + 1)) < Sbar a x n ω}) := by
  have hr1 : 1 < 2 * (3 + ε) / (6 + ε) := by
    rw [one_lt_div (by linarith)]
    linarith
  have hr0 : 0 < 2 * (3 + ε) / (6 + ε) := by linarith
  have hlogr : 0 < Real.log (2 * (3 + ε) / (6 + ε)) := Real.log_pos hr1
  have hgrow := BG9817455d.sol a ha_pos ε hε nk h411 h412 h414
  have h0 : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) := by
    have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)
    refine this.congr (fun k => ?_)
    push_cast
    ring
  have hg := h0.mul_left (2 * (1 / Real.log (2 * (3 + ε) / (6 + ε)) ^ 2))
  refine Summable.of_norm_bounded_eventually_nat hg ?_
  obtain ⟨K, hK⟩ : ∃ K : ℕ, 1 / Real.log (2 * (3 + ε) / (6 + ε)) ≤ K := exists_nat_ge _
  rw [Filter.eventually_atTop]
  refine ⟨K, fun k hk => ?_⟩
  have hk1 : 1 ≤ ((k : ℝ) + 1) * Real.log (2 * (3 + ε) / (6 + ε)) := by
    have hKk : (K : ℝ) ≤ k := by exact_mod_cast hk
    rw [div_le_iff₀ hlogr] at hK
    nlinarith
  have hN0 := hnk (k + 1) (by omega)
  have hgk := hgrow (k + 2) (by omega)
  rw [show k + 2 - 1 = k + 1 by omega] at hgk
  have hlogA : ((k : ℝ) + 1) * Real.log (2 * (3 + ε) / (6 + ε)) < Real.log (A a (nk (k + 2))) := by
    have := Real.log_lt_log (pow_pos hr0 _) hgk
    rwa [Real.log_pow, Nat.cast_add, Nat.cast_one] at this
  have hL : 1 ≤ Real.log (A a (nk (k + 2))) := by linarith
  have h414k := h414 (k + 2) (by omega)
  rw [show k + 2 - 1 = k + 1 by omega] at h414k
  have hlt : nk 1 < nk (k + 2) :=
    lt_of_lt_of_le (hnk 1 le_rfl).2 (nk_mono nk hnk (by omega) (by omega))
  have hterm := term_le ℱ x hx hbd a ha_pos ha_mono ε hε hε1 (nk (k + 1)) (nk (k + 2)) hN0.1
    hN0.2 h414k.2.1 (h413 _ hlt) hL
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  refine hterm.trans ?_
  have hL2 : (((k : ℝ) + 1) * Real.log (2 * (3 + ε) / (6 + ε))) ^ 2
      ≤ Real.log (A a (nk (k + 2))) ^ 2 := pow_le_pow_left₀ (by positivity) hlogA.le 2
  have h1 : 1 / Real.log (A a (nk (k + 2))) ^ 2
      ≤ 1 / (((k : ℝ) + 1) * Real.log (2 * (3 + ε) / (6 + ε))) ^ 2 :=
    one_div_le_one_div_of_le (by positivity) hL2
  calc 2 * (1 / Real.log (A a (nk (k + 2))) ^ 2)
      ≤ 2 * (1 / (((k : ℝ) + 1) * Real.log (2 * (3 + ε) / (6 + ε))) ^ 2) := by linarith
    _ = 2 * (1 / Real.log (2 * (3 + ε) / (6 + ε)) ^ 2) * (1 / ((k : ℝ) + 1) ^ 2) := by
      rw [mul_pow]
      field_simp

/-- One-sided strong law for a fixed `ε ∈ (0, 1]`. -/
theorem one_sided {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (x : ℕ → Ω → ℝ)
    (hx : AzumaWeightedSums.IteratedLog.IsMartingaleDiff μ ℱ x)
    (hbd : ∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂μ, |x n ω| ≤ 1)
    (a : ℕ → ℝ) (ha_pos : ∀ n : ℕ, 1 ≤ n → 0 < a n) (ha_mono : ∀ n : ℕ, 1 ≤ n → a n ≤ a (n + 1))
    (h49 : (fun n => a n / A a n) =o[atTop] (fun n => 1 / Real.log (Real.log (A a n))))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, Sbar a x n ω ≤ ε * A a n := by
  obtain ⟨nk, hnk, h411, h412, h413, h414⟩ := BS22e216a2.sol a ha_pos ha_mono h49 ε hε
  have hsum := summable_blocks ℱ x hx hbd a ha_pos ha_mono ε hε hε1 nk hnk h411 h412 h413 h414
  have hBC : ∀ᵐ ω ∂μ, ∀ᶠ k in atTop, ω ∉ {ω | ∃ n ∈ Finset.Ioc (nk (k + 1)) (nk (k + 2)),
      ε * A a (nk (k + 1)) < Sbar a x n ω} := by
    apply ae_eventually_notMem
    have e : ∀ k : ℕ, μ {ω | ∃ n ∈ Finset.Ioc (nk (k + 1)) (nk (k + 2)),
        ε * A a (nk (k + 1)) < Sbar a x n ω}
        = ENNReal.ofReal (μ.real {ω | ∃ n ∈ Finset.Ioc (nk (k + 1)) (nk (k + 2)),
        ε * A a (nk (k + 1)) < Sbar a x n ω}) := fun k => (ofReal_measureReal (measure_ne_top μ _)).symm
    rw [tsum_congr e, ← ENNReal.ofReal_tsum_of_nonneg (fun k => measureReal_nonneg) hsum]
    exact ENNReal.ofReal_ne_top
  filter_upwards [hBC] with ω hω
  obtain ⟨K, hK⟩ := eventually_atTop.1 hω
  have hb : ∀ k : ℕ, K ≤ k → ∀ n ∈ Finset.Ioc (nk (k + 1)) (nk (k + 2)),
      Sbar a x n ω ≤ ε * A a n := by
    intro k hk n hn
    by_contra hc
    rw [not_le] at hc
    have hm : A a (nk (k + 1)) ≤ A a n := BG9817455d.A_mono a ha_pos (Finset.mem_Ioc.1 hn).1.le
    exact hK k hk ⟨n, hn, lt_of_le_of_lt (mul_le_mul_of_nonneg_left hm hε.le) hc⟩
  have hblock : ∀ k : ℕ, K ≤ k → ∀ n ∈ Finset.Ioc (nk (K + 1)) (nk (k + 2)),
      Sbar a x n ω ≤ ε * A a n := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact hb K le_rfl
    | succ k hk ih =>
      intro n hn
      rw [Finset.mem_Ioc] at hn
      by_cases hle : n ≤ nk (k + 2)
      · exact ih n (Finset.mem_Ioc.2 ⟨hn.1, hle⟩)
      · exact hb (k + 1) (by omega) n (Finset.mem_Ioc.2 ⟨lt_of_not_ge hle, hn.2⟩)
  rw [eventually_atTop]
  refine ⟨nk (K + 1) + 1, fun n hn => hblock (n + K) (by omega) n (Finset.mem_Ioc.2 ⟨by omega, ?_⟩)⟩
  have := nk_ge nk hnk (n + K + 2) (by omega)
  omega

theorem sbar_neg {Ω : Type*} (a : ℕ → ℝ) (x : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    Sbar a (fun n ω => -x n ω) n ω = -Sbar a x n ω := by
  simp only [Sbar, mul_neg, Finset.sum_neg_distrib]

theorem main3 {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (x : ℕ → Ω → ℝ)
    (hx : AzumaWeightedSums.IteratedLog.IsMartingaleDiff μ ℱ x) (hbd : ∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂μ, |x n ω| ≤ 1)
    (a : ℕ → ℝ) (ha_pos : ∀ n : ℕ, 1 ≤ n → 0 < a n)
    (ha_mono : ∀ n : ℕ, 1 ≤ n → a n ≤ a (n + 1))
    (h49 : (fun n => a n / A a n) =o[atTop] (fun n => 1 / Real.log (Real.log (A a n)))) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => Sbar a x n ω / A a n) atTop (𝓝 0) := by
  have hnegx : AzumaWeightedSums.IteratedLog.IsMartingaleDiff μ ℱ (fun n ω => -x n ω) := by
    intro n hn
    obtain ⟨h1, h2, h3⟩ := hx n hn
    refine ⟨h1.neg, h2.neg, ?_⟩
    have := condExp_neg (μ := μ) (x n) (ℱ (n - 1))
    show μ[-x n | ℱ (n - 1)] =ᵐ[μ] 0
    filter_upwards [this, h3] with ω hω h3ω
    rw [hω, Pi.neg_apply, h3ω]
    simp
  have hbdneg : ∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂μ, |(fun n ω => -x n ω) n ω| ≤ 1 :=
    fun n hn => (hbd n hn).mono fun ω h => by simpa [abs_neg] using h
  have hall : ∀ᵐ ω ∂μ, ∀ m : ℕ,
      (∀ᶠ n in atTop, Sbar a x n ω ≤ 1 / ((m : ℝ) + 1) * A a n) ∧
      (∀ᶠ n in atTop, Sbar a (fun n ω => -x n ω) n ω ≤ 1 / ((m : ℝ) + 1) * A a n) := by
    rw [ae_all_iff]
    intro m
    have hε : 0 < 1 / ((m : ℝ) + 1) := by positivity
    have hε1 : 1 / ((m : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    filter_upwards [one_sided ℱ x hx hbd a ha_pos ha_mono h49 _ hε hε1,
      one_sided ℱ (fun n ω => -x n ω) hnegx hbdneg a ha_pos ha_mono h49 _ hε hε1] with ω h1 h2
    exact ⟨h1, h2⟩
  filter_upwards [hall] with ω hω
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 ((hω m).1.and (hω m).2)
  refine ⟨max N1 1, fun n hn => ?_⟩
  obtain ⟨h1, h2⟩ := hN1 n (le_of_max_le_left hn)
  rw [sbar_neg] at h2
  have hApos : 0 < A a n := BG9817455d.A_pos a ha_pos (le_of_max_le_right hn)
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hApos, div_lt_iff₀ hApos]
  have habs : |Sbar a x n ω| ≤ 1 / ((m : ℝ) + 1) * A a n := abs_le.2 ⟨by linarith, h1⟩
  nlinarith [mul_lt_mul_of_pos_right hm hApos]

end P0bb8376a

open MeasureTheory Filter Asymptotics Topology AzumaWeightedSums.StrongLaw in
theorem solution {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (x : ℕ → Ω → ℝ)
    (hx : AzumaWeightedSums.IteratedLog.IsMartingaleDiff μ ℱ x) (hbd : ∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂μ, |x n ω| ≤ 1)
    (a : ℕ → ℝ) (ha_pos : ∀ n : ℕ, 1 ≤ n → 0 < a n)
    (ha_mono : ∀ n : ℕ, 1 ≤ n → a n ≤ a (n + 1))
    (h49 : (fun n => a n / A a n) =o[atTop] (fun n => 1 / Real.log (Real.log (A a n)))) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => Sbar a x n ω / A a n) atTop (𝓝 0) := by
  exact P0bb8376a.main3 ℱ x hx hbd a ha_pos ha_mono h49
