-- Prove2me | solution 1 for Farey.card_pairs_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-10T10:48:53.042535+00:00
-- url     : https://prove2.me/submissions/eb98ae8b-df72-45dc-b381-48361d535109

import Definitions.Def_Farey
import Mathlib

theorem solution (P : ℕ) : (Farey.pairs P).card ≤ P ^ 2 := by
  unfold Farey.pairs
  refine (Finset.card_biUnion_le).trans ?_
  have h : ∀ q ∈ Finset.Icc 1 P,
      (((Finset.Icc 1 q).filter fun a => Nat.Coprime a q).image fun a => (q, a)).card ≤ P := by
    intro q hq
    refine Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans ?_)
    rw [Nat.card_Icc]
    exact (Finset.mem_Icc.mp hq).2.trans (by omega)
  refine (Finset.sum_le_sum h).trans ?_
  rw [Finset.sum_const, Nat.card_Icc, smul_eq_mul, Nat.add_sub_cancel, pow_two]
