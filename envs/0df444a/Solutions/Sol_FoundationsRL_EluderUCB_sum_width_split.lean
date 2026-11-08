-- Prove2me | solution 1 for FoundationsRL.EluderUCB.sum_width_split
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:40:39.279234+00:00
-- url     : https://prove2.me/submissions/e9622e7b-77d0-4550-9481-8cd72da0d14e

import Mathlib
import Definitions.Def_FoundationsRL_EluderUCB_width

open scoped Classical

open FoundationsRL.EluderUCB in
theorem solution {Act : Type*} (F : Set (Act → ℝ))
    (hF : ∀ f ∈ F, ∀ p, f p ∈ Set.Icc (0 : ℝ) 1) (fstar : Act → ℝ) (hfstar : fstar ∈ F)
    (β : ℝ) (hβ : 0 ≤ β) (T : ℕ) (π : ℕ → Act) (ε : ℝ) (hε : 0 < ε) :
    ∑ t ∈ Finset.Icc 1 T, (width F fstar (4 * β) π t (π t)).toReal ≤
      ∑ t ∈ Finset.Icc 1 T, ((width F fstar (4 * β) π t (π t)).toReal *
        (if ε < (width F fstar (4 * β) π t (π t)).toReal then 1 else 0)) + ε * T := by
  have hT : ε * (T : ℝ) = ∑ t ∈ Finset.Icc 1 T, ε := by
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    simp only [Nat.add_sub_cancel]
    ring
  rw [hT, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro t _
  by_cases hw : ε < (width F fstar (4 * β) π t (π t)).toReal
  · rw [if_pos hw]; linarith
  · rw [if_neg hw]; push_neg at hw; linarith
