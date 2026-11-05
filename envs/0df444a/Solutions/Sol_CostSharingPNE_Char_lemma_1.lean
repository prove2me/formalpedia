-- Prove2me | solution 1 for CostSharingPNE.Char.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T16:24:51.72619+00:00
-- url     : https://prove2.me/submissions/edda22ca-fcd2-49ee-9b0c-7dd8cc008245

import Mathlib
import Definitions.Def_CostSharingPNE_Char_Setting
import Definitions.Def_CostSharingPNE_Char_WeightSystem
import Definitions.Def_CostSharingPNE_Char_Basis
import Theorems.Thm_CostSharingPNE_Char_lemma_2

open CostSharingPNE.Char

theorem solution (n : ℕ) (hn : 1 < n) (W : Welfare n) (f : Welfare n → Rule n)
    (hbb : IsBudgetBalanced (f W) W) (hpne : GuaranteesPNE {W} f) :
    ∀ S : Finset (Fin n), coalitionsIn W S = ∅ → ∀ i ∈ S, f W i S = 0 := by
  intro S hS i hi
  apply lemma_2 n hn W f hbb hpne S i
  have : contributing W S = ∅ := by
    unfold contributing; rw [hS]; rfl
  rw [this, Finset.sdiff_empty]
  exact hi
