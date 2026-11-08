-- Prove2me | solution 1 for DDNNFNeg.proposition_5_1_three_conditions
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T05:12:34.093969+00:00
-- url     : https://prove2.me/submissions/7feaa859-b1e3-44f0-8414-7a82bce36f39

import Mathlib
import Definitions.Def_DDNNFNeg_fG

open DDNNFNeg in
theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (c : Sym2 (Fin n) → Fin 3) (x : Fin n → Bool) :
    (fG G c x = true ↔
      (HasColor G c x 0 ∧ ¬ HasColor G c x 1) ∨ (HasColor G c x 1 ∧ ¬ HasColor G c x 2) ∨
        (HasColor G c x 2 ∧ ¬ HasColor G c x 0)) ∧
    ¬ ((HasColor G c x 0 ∧ ¬ HasColor G c x 1) ∧ (HasColor G c x 1 ∧ ¬ HasColor G c x 2)) ∧
    ¬ ((HasColor G c x 0 ∧ ¬ HasColor G c x 1) ∧ (HasColor G c x 2 ∧ ¬ HasColor G c x 0)) ∧
    ¬ ((HasColor G c x 1 ∧ ¬ HasColor G c x 2) ∧ (HasColor G c x 2 ∧ ¬ HasColor G c x 0)) := by
  have hE : HasEdge G x ↔ HasColor G c x 0 ∨ HasColor G c x 1 ∨ HasColor G c x 2 := by
    unfold HasEdge HasColor
    constructor
    · rintro ⟨e, he, hv⟩
      obtain h | h | h : c e = 0 ∨ c e = 1 ∨ c e = 2 := by
        generalize c e = k
        fin_cases k <;> simp
      · exact Or.inl ⟨e, he, hv, h⟩
      · exact Or.inr (Or.inl ⟨e, he, hv, h⟩)
      · exact Or.inr (Or.inr ⟨e, he, hv, h⟩)
    · rintro (⟨e, he, hv, _⟩ | ⟨e, he, hv, _⟩ | ⟨e, he, hv, _⟩) <;> exact ⟨e, he, hv⟩
  refine ⟨?_, by tauto, by tauto, by tauto⟩
  unfold fG
  rw [decide_eq_true_iff, hE, Finset.card_filter, Fin.sum_univ_three]
  by_cases h0 : HasColor G c x 0 <;> by_cases h1 : HasColor G c x 1 <;>
    by_cases h2 : HasColor G c x 2 <;> simp [h0, h1, h2]
