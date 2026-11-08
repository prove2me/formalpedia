-- Prove2me | solution 1 for FeedbackSwitching.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T00:37:21.114451+00:00
-- url     : https://prove2.me/submissions/b037701d-804d-49c5-957b-d58f04929bd7

import Mathlib
import Definitions.Def_FeedbackSwitching_StronglyRevealing
import Definitions.Def_FeedbackSwitching_IsTournament

open FeedbackSwitching in
theorem solution :
    (∀ (K : ℕ) (G : FeedbackGraph K),
      StronglyRevealing G ↔ ∃ (A : Fin K → Fin K → Prop) (L : Fin K → Prop),
        IsSpanningSOTournament G A L) ∧
    ∃ rule : Prop → Prop → Prop → Prop → Prop,
      ∀ (K : ℕ) (G : FeedbackGraph K), StronglyRevealing G →
        IsObservedOrientation G (orientByRule rule G) := by
  refine ⟨fun K G => ⟨fun hSR => ?_, fun ⟨A, L, hT, hAG, hL, hcov⟩ => ?_⟩, ?_⟩
  · refine ⟨fun i j => G i i ∧ G i j ∧ (¬ G j j ∨ ¬ G j i ∨ i < j), fun i => G i i,
      ⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · intro v hv
      exact (hv.2.2.elim (fun h => h hv.1) (fun h => h.elim (fun h' => h' hv.1)
        (fun h' => lt_irrefl _ h')))
    · intro u v huv
      show (G u u ∧ G u v ∧ (¬ G v v ∨ ¬ G v u ∨ u < v)) ↔
        ¬ (G v v ∧ G v u ∧ (¬ G u u ∨ ¬ G u v ∨ v < u))
      constructor
      · rintro ⟨h1, h2, h3⟩ ⟨h4, h5, h6⟩
        rcases h3 with h3 | h3 | h3
        · exact h3 h4
        · exact h3 h5
        · rcases h6 with h6 | h6 | h6
          · exact h6 h1
          · exact h6 h2
          · exact lt_asymm h3 h6
      · intro hn
        rcases hSR u v huv with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · refine ⟨h1, h2, ?_⟩
          by_cases hvv : G v v
          · by_cases hvu : G v u
            · right; right
              rcases lt_or_gt_of_ne huv with h | h
              · exact h
              · exact absurd ⟨hvv, hvu, Or.inr (Or.inr h)⟩ hn
            · right; left; exact hvu
          · left; exact hvv
        · by_cases huu : G u u
          · by_cases huv' : G u v
            · refine ⟨huu, huv', ?_⟩
              right; right
              rcases lt_or_gt_of_ne huv with h | h
              · exact h
              · exact absurd ⟨h1, h2, Or.inr (Or.inr h)⟩ hn
            · exact absurd ⟨h1, h2, Or.inr (Or.inl huv')⟩ hn
          · exact absurd ⟨h1, h2, Or.inl huu⟩ hn
    · intro i j h; exact h.2.1
    · intro i h; exact h
    · intro i
      by_cases hii : G i i
      · left; exact hii
      · right
        intro j hji
        rcases hSR j i hji with ⟨h1, h2⟩ | ⟨h1, _⟩
        · exact ⟨h1, h2, Or.inl hii⟩
        · exact absurd h1 hii
  · intro i j hij
    have htour := hT.2 i j hij
    change A i j ↔ ¬ A j i at htour
    by_cases hA : A i j
    · left
      refine ⟨?_, hAG i j hA⟩
      rcases hcov i with h | h
      · exact hL i h
      · exact absurd (h j (Ne.symm hij)) (htour.mp hA)
    · right
      have hA' : A j i := by
        by_contra h; exact hA (htour.mpr h)
      refine ⟨?_, hAG j i hA'⟩
      rcases hcov j with h | h
      · exact hL j h
      · exact absurd (h i hij) hA
  · refine ⟨fun a b _ _ => a ∧ b, fun K G hSR => ⟨⟨?_, ?_⟩, ?_⟩⟩
    · intro v hv
      change (v < v ∧ _) ∨ (v < v ∧ _) at hv
      rcases hv with h | h
      · exact lt_irrefl _ h.1
      · exact lt_irrefl _ h.1
    · intro u v huv
      change ((u < v ∧ (G u u ∧ G u v)) ∨ (v < u ∧ ¬ (G v v ∧ G v u))) ↔
        ¬ ((v < u ∧ (G v v ∧ G v u)) ∨ (u < v ∧ ¬ (G u u ∧ G u v)))
      rcases lt_or_gt_of_ne huv with h | h
      · have h' : ¬ v < u := lt_asymm h
        simp only [h, h', true_and, false_and, or_false, false_or, not_not]
      · have h' : ¬ u < v := lt_asymm h
        simp only [h, h', true_and, false_and, or_false, false_or]
    · intro s j hsj
      change (s < j ∧ (G s s ∧ G s j)) ∨ (j < s ∧ ¬ (G j j ∧ G j s)) at hsj
      rcases hsj with ⟨_, h⟩ | ⟨hjs, h⟩
      · exact h
      · rcases hSR s j (ne_of_gt hjs) with h' | h'
        · exact h'
        · exact absurd h' h
