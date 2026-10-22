-- Prove2me | solution 1 for ContJRP.Align.observation_2_3_first_segment_active
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:00:48.574999+00:00
-- url     : https://prove2.me/submissions/79389786-bce6-4f44-a7cb-f13eb6f45337

import Mathlib
import Definitions.Def_ContJRP_Align_Policy

set_option autoImplicit false
open Classical ContJRP.Align

theorem solution (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    {n : ℕ} [NeZero n] (Tstar : Fin n → ℝ) (hTstar : ∀ i, 0 < Tstar i)
    (Tt : ℝ) (hTt1 : (1 - ε / 2) * tmin Tstar ≤ Tt) (hTt2 : Tt ≤ tmin Tstar) :
    0 ∈ active ε Tt Tstar := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty Tstar
  have hmin : tmin Tstar = Tstar i := hi
  have hpos : 0 < Tstar i := hTstar i
  rw [hmin] at hTt1 hTt2
  have hTtpos : 0 < Tt := by nlinarith
  unfold active
  rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · unfold numSegments
    have hne : {L : ℕ | 1 / ε < (1 + ε) ^ L}.Nonempty :=
      pow_unbounded_of_one_lt (1 / ε) (by linarith)
    have hmem := Nat.sInf_mem hne
    have hne0 : sInf {L : ℕ | 1 / ε < (1 + ε) ^ L} ≠ 0 := by
      intro h0
      rw [h0] at hmem
      simp only [Set.mem_setOf_eq, pow_zero] at hmem
      have : 2 < 1 / ε := by
        rw [lt_div_iff₀ hε0]; linarith
      linarith
    omega
  · refine ⟨i, ?_⟩
    unfold seg
    simp only [pow_zero, one_mul, zero_add, pow_one]
    refine ⟨hTt2, ?_⟩
    have h : (1 + ε) * ((1 - ε / 2) * Tstar i) ≤ (1 + ε) * Tt :=
      mul_le_mul_of_nonneg_left hTt1 (by linarith)
    have h3 : 0 < ε * (1 - ε) * Tstar i := mul_pos (mul_pos hε0 (by linarith)) hpos
    nlinarith [h, h3]
