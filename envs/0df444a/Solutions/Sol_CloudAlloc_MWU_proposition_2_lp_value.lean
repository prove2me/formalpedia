-- Prove2me | solution 1 for CloudAlloc.MWU.proposition_2_lp_value
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T23:45:46.055182+00:00
-- url     : https://prove2.me/submissions/90b6e45d-c6b2-4eeb-906c-1ec6c8924a25

import Mathlib

namespace Aux_CloudAlloc_prop2

/-- backlog of the greedy proportional server -/
noncomputable def B (N : ℕ) (ε : ℝ) (L : ℕ → Fin N → ℝ) : ℕ → Fin N → ℝ
  | 0 => fun _ => 0
  | t + 1 => fun i => (B N ε L t i + L t i) *
      (1 - min 1 ((1 - ε) / ∑ j, (B N ε L t j + L t j)))

noncomputable def cc (N : ℕ) (ε : ℝ) (L : ℕ → Fin N → ℝ) (t : ℕ) : ℝ :=
  min 1 ((1 - ε) / ∑ j, (B N ε L t j + L t j))

noncomputable def ww (N : ℕ) (ε : ℝ) (L : ℕ → Fin N → ℝ) (t : ℕ) (i : Fin N) : ℝ :=
  (B N ε L t i + L t i) * cc N ε L t

theorem B_succ (N : ℕ) (ε : ℝ) (L : ℕ → Fin N → ℝ) (t : ℕ) (i : Fin N) :
    B N ε L (t + 1) i = B N ε L t i + L t i - ww N ε L t i := by
  show (B N ε L t i + L t i) * (1 - min 1 ((1 - ε) / ∑ j, (B N ε L t j + L t j))) = _
  unfold ww cc
  ring

theorem cc_le (N : ℕ) (ε : ℝ) (L : ℕ → Fin N → ℝ) (t : ℕ) : cc N ε L t ≤ 1 := min_le_left _ _

theorem B_nonneg (N : ℕ) (ε : ℝ) (L : ℕ → Fin N → ℝ) (hL : ∀ t i, 0 ≤ L t i) :
    ∀ t i, 0 ≤ B N ε L t i := by
  intro t
  induction t with
  | zero => intro i; exact le_refl _
  | succ t ih =>
    intro i
    show 0 ≤ (B N ε L t i + L t i) * (1 - min 1 ((1 - ε) / ∑ j, (B N ε L t j + L t j)))
    apply mul_nonneg
    · linarith [ih i, hL t i]
    · linarith [min_le_left 1 ((1 - ε) / ∑ j, (B N ε L t j + L t j))]

theorem tot_nonneg (N : ℕ) (ε : ℝ) (L : ℕ → Fin N → ℝ) (hL : ∀ t i, 0 ≤ L t i) (t : ℕ) :
    0 ≤ ∑ j, (B N ε L t j + L t j) :=
  Finset.sum_nonneg (fun j _ => by linarith [B_nonneg N ε L hL t j, hL t j])

theorem cc_nonneg (N : ℕ) (ε : ℝ) (hε1 : ε < 1) (L : ℕ → Fin N → ℝ) (hL : ∀ t i, 0 ≤ L t i)
    (t : ℕ) : 0 ≤ cc N ε L t := by
  unfold cc
  apply le_min zero_le_one
  exact div_nonneg (by linarith) (tot_nonneg N ε L hL t)

theorem ww_nonneg (N : ℕ) (ε : ℝ) (hε1 : ε < 1) (L : ℕ → Fin N → ℝ) (hL : ∀ t i, 0 ≤ L t i)
    (t : ℕ) (i : Fin N) : 0 ≤ ww N ε L t i := by
  unfold ww
  exact mul_nonneg (by linarith [B_nonneg N ε L hL t i, hL t i]) (cc_nonneg N ε hε1 L hL t)

theorem sw_eq (N : ℕ) (ε : ℝ) (L : ℕ → Fin N → ℝ) (t : ℕ) :
    ∑ i, ww N ε L t i = (∑ j, (B N ε L t j + L t j)) * cc N ε L t := by
  unfold ww
  rw [Finset.sum_mul]

theorem sw_cases (N : ℕ) (ε : ℝ) (hε1 : ε < 1) (L : ℕ → Fin N → ℝ) (hL : ∀ t i, 0 ≤ L t i)
    (t : ℕ) : ∑ i, ww N ε L t i ≤ 1 - ε ∧
      (∑ i, ww N ε L t i = 1 - ε ∨ ∑ i, ww N ε L t i = ∑ j, (B N ε L t j + L t j)) := by
  rw [sw_eq]
  have htot := tot_nonneg N ε L hL t
  set tot := ∑ j, (B N ε L t j + L t j) with htot_def
  unfold cc
  rw [← htot_def]
  rcases eq_or_lt_of_le htot with h0 | hpos
  · rw [← h0]
    simp only [div_zero, zero_mul]
    exact ⟨by linarith, Or.inr (by trivial)⟩
  · by_cases hle : tot ≤ 1 - ε
    · have h1 : 1 ≤ (1 - ε) / tot := by rw [le_div_iff₀ hpos]; linarith
      rw [min_eq_left h1, mul_one]
      exact ⟨hle, Or.inr rfl⟩
    · push_neg at hle
      have h1 : (1 - ε) / tot ≤ 1 := by rw [div_le_iff₀ hpos]; linarith
      have hcan : tot * ((1 - ε) / tot) = 1 - ε := by field_simp
      rw [min_eq_right h1, hcan]
      exact ⟨le_refl _, Or.inl rfl⟩

theorem B_eq (N : ℕ) (ε : ℝ) (L : ℕ → Fin N → ℝ) :
    ∀ t i, B N ε L t i = ∑ s ∈ Finset.range t, (L s i - ww N ε L s i) := by
  intro t
  induction t with
  | zero => intro i; show (0 : ℝ) = _; simp
  | succ t ih =>
    intro i
    rw [B_succ, ih i, Finset.sum_range_succ]
    ring

theorem cons (N : ℕ) (ε : ℝ) (L : ℕ → Fin N → ℝ) (T : ℕ) :
    ∑ i, B N ε L T i = ∑ s ∈ Finset.range T, ∑ i, L s i - ∑ s ∈ Finset.range T, ∑ i, ww N ε L s i := by
  rw [Finset.sum_congr rfl (fun i _ => B_eq N ε L T i), Finset.sum_comm, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [Finset.sum_sub_distrib]

theorem greedy_value {N : ℕ} {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (T : ℕ)
    {L : ℕ → Fin N → ℝ} (hL : ∀ t i, 0 ≤ L t i) :
    ∃ t0 ∈ Finset.range (T + 1), ∑ t ∈ Finset.range T, ∑ i, ww N ε L t i =
      ∑ s ∈ Finset.range t0, ∑ i, L s i + (1 - ε) * ((T : ℝ) - t0) := by
  induction T with
  | zero => exact ⟨0, by simp, by simp⟩
  | succ T ih =>
    obtain ⟨t0, ht0, heq⟩ := ih
    obtain ⟨_, hc⟩ := sw_cases N ε hε1 L hL T
    rcases hc with h | h
    · refine ⟨t0, by rw [Finset.mem_range] at ht0 ⊢; omega, ?_⟩
      rw [Finset.sum_range_succ, heq, h]
      push_cast
      ring
    · refine ⟨T + 1, by simp, ?_⟩
      have hcons := cons N ε L T
      rw [Finset.sum_range_succ, h, Finset.sum_range_succ (fun s => ∑ i, L s i)]
      have : ∑ j, (B N ε L T j + L T j) = ∑ j, B N ε L T j + ∑ j, L T j := Finset.sum_add_distrib
      rw [this, hcons]
      push_cast
      ring

end Aux_CloudAlloc_prop2

open Aux_CloudAlloc_prop2 in
theorem solution {N : ℕ} {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (T : ℕ)
    {L : ℕ → Fin N → ℝ} (hL : ∀ t i, 0 ≤ L t i) :
    IsGreatest
      ((fun w : ℕ → Fin N → ℝ => ∑ t ∈ Finset.range T, ∑ i, w t i) ''
        {w | (∀ t < T, ∀ i, ∑ s ∈ Finset.range (t + 1), w s i ≤ ∑ s ∈ Finset.range (t + 1), L s i) ∧
          (∀ t < T, ∑ i, w t i ≤ 1 - ε) ∧ (∀ t < T, ∀ i, 0 ≤ w t i)})
      ((Finset.range (T + 1)).inf' ⟨0, Finset.mem_range.mpr (Nat.succ_pos T)⟩
        (fun t => ∑ s ∈ Finset.range t, ∑ i, L s i + (1 - ε) * ((T : ℝ) - t))) := by
  -- upper bound for every feasible allocation
  have hub : ∀ w : ℕ → Fin N → ℝ,
      (∀ t < T, ∀ i, ∑ s ∈ Finset.range (t + 1), w s i ≤ ∑ s ∈ Finset.range (t + 1), L s i) →
      (∀ t < T, ∑ i, w t i ≤ 1 - ε) →
      ∀ t0 ∈ Finset.range (T + 1), ∑ t ∈ Finset.range T, ∑ i, w t i ≤
        ∑ s ∈ Finset.range t0, ∑ i, L s i + (1 - ε) * ((T : ℝ) - t0) := by
    intro w h1 h2 t0 ht0
    rw [Finset.mem_range] at ht0
    rw [← Finset.sum_range_add_sum_Ico _ (show t0 ≤ T by omega)]
    have hA : ∑ t ∈ Finset.range t0, ∑ i, w t i ≤ ∑ s ∈ Finset.range t0, ∑ i, L s i := by
      rcases Nat.eq_zero_or_pos t0 with h0 | hpos
      · subst h0; simp
      · obtain ⟨t1, rfl⟩ : ∃ t1, t0 = t1 + 1 := ⟨t0 - 1, by omega⟩
        calc ∑ t ∈ Finset.range (t1 + 1), ∑ i, w t i
            = ∑ i, ∑ t ∈ Finset.range (t1 + 1), w t i := Finset.sum_comm
          _ ≤ ∑ i, ∑ t ∈ Finset.range (t1 + 1), L t i :=
            Finset.sum_le_sum (fun i _ => h1 t1 (by omega) i)
          _ = ∑ s ∈ Finset.range (t1 + 1), ∑ i, L s i := Finset.sum_comm
    have hB : ∑ t ∈ Finset.Ico t0 T, ∑ i, w t i ≤ (1 - ε) * ((T : ℝ) - t0) := by
      have : ∑ t ∈ Finset.Ico t0 T, ∑ i, w t i ≤ ∑ t ∈ Finset.Ico t0 T, (1 - ε) :=
        Finset.sum_le_sum (fun t ht => h2 t (Finset.mem_Ico.mp ht).2)
      rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub (show t0 ≤ T by omega)] at this
      linarith
    linarith
  obtain ⟨t0, ht0, heq⟩ := greedy_value hε hε1 T hL
  have hfeas :
      (∀ t < T, ∀ i, ∑ s ∈ Finset.range (t + 1), ww N ε L s i ≤ ∑ s ∈ Finset.range (t + 1), L s i) ∧
      (∀ t < T, ∑ i, ww N ε L t i ≤ 1 - ε) ∧ (∀ t < T, ∀ i, 0 ≤ ww N ε L t i) := by
    refine ⟨fun t _ i => ?_, fun t _ => (sw_cases N ε hε1 L hL t).1,
      fun t _ i => ww_nonneg N ε hε1 L hL t i⟩
    have h1 := B_nonneg N ε L hL (t + 1) i
    rw [B_eq, Finset.sum_sub_distrib] at h1
    linarith
  refine ⟨⟨ww N ε L, hfeas, ?_⟩, ?_⟩
  · show ∑ t ∈ Finset.range T, ∑ i, ww N ε L t i = _
    apply le_antisymm
    · apply Finset.le_inf'
      exact hub (ww N ε L) hfeas.1 hfeas.2.1
    · rw [heq]
      exact Finset.inf'_le _ ht0
  · rintro x ⟨w, ⟨h1, h2, _⟩, rfl⟩
    apply Finset.le_inf'
    exact hub w h1 h2
