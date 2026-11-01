-- Prove2me | solution 1 for BudgetAgg.NashChar.theorem_3_uniqueness
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T20:50:36.424976+00:00
-- url     : https://prove2.me/submissions/8981c54a-56a0-4126-ae78-f90266e1afe2

import Mathlib
import Definitions.Def_BudgetAgg_NashChar_Setting
import Theorems.Thm_BudgetAgg_NashChar_proposition_3
import Theorems.Thm_BudgetAgg_NashChar_lemma_9
import Theorems.Thm_BudgetAgg_NashChar_lemma_10
import Theorems.Thm_BudgetAgg_NashChar_lemma_11

open BudgetAgg.NashChar

theorem solution {n m : ℕ} [NeZero n] [NeZero m]
    (f : Mechanism n m) (hf_cont : Continuous f) (hf_gsp : IsGroupSP f)
    (hf_core : ∀ P, IsCoreFairShare P (f P)) :
    ∀ P, IsNashOutcome P (f P).1 := by
  intro P
  have hf_eff : ∀ P, IsEfficient P (f P) := fun P => proposition_3 P (f P) (hf_core P)
  obtain ⟨Ps, hPs, hfPs, hcrit⟩ := lemma_9 f hf_cont hf_gsp hf_eff P
  have hsupp : ∀ i j, j ∉ crit (Ps i) (f P).1 → (Ps i).1 j = 0 := by
    intro i j hj
    rw [hcrit i] at hj
    rw [hPs i, starPeak, if_neg hj]
  have hcore : IsCoreFairShare Ps (f P) := hfPs ▸ hf_core Ps
  exact lemma_11 Ps P (f P) (lemma_10 Ps (f P) hsupp hcore) hcrit

