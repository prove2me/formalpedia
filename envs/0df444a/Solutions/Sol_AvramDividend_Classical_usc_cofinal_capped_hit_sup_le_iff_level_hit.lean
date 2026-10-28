-- Prove2me | solution 1 for AvramDividend.Classical.usc_cofinal_capped_hit_sup_le_iff_level_hit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:10:01.24502+00:00
-- url     : https://prove2.me/submissions/df459655-7acc-47a4-be0a-abc28c9c0804

import Theorems.Thm_AvramDividend_Classical_usc_capped_first_closed_hit_le_iff_prefix_hit

open AvramDividend.Classical Set
open scoped NNReal
theorem solution
    (f : ℝ≥0 → ℝ) (caps : ℕ → ℝ≥0) (x : ℝ)
    (husc : ∀ H : ℝ≥0, UpperSemicontinuousOn f (Icc 0 H))
    (hcofinal : ∀ t : ℝ≥0, ∃ n : ℕ, t < caps n)
    (t : ℝ≥0) :
    (⨆ n : ℕ, WithTop.some
      (sInf ((Icc (0 : ℝ≥0) (caps n) ∩ f ⁻¹' Ici x) ∪ {caps n}))) ≤
        (t : WithTop ℝ≥0) ↔
      ∃ s : ℝ≥0, s ≤ t ∧ x ≤ f s := by
  rw [iSup_le_iff]
  simp only [WithTop.coe_le_coe]
  constructor
  · intro h
    obtain ⟨n, hn⟩ := hcofinal t
    exact (usc_capped_first_closed_hit_le_iff_prefix_hit f (caps n) t x (husc _) hn).1 (h n)
  · intro h n
    by_cases hn : t < caps n
    · exact (usc_capped_first_closed_hit_le_iff_prefix_hit f (caps n) t x (husc _) hn).2 h
    · push_neg at hn
      exact le_trans (csInf_le (OrderBot.bddBelow _) (Or.inr rfl)) hn
