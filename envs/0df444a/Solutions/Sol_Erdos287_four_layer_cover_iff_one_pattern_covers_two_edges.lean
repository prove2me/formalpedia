-- Prove2me | solution 1 for Erdos287.four_layer_cover_iff_one_pattern_covers_two_edges
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T13:52:14.651839+00:00
-- url     : https://prove2.me/submissions/51940186-57ba-4556-88c6-01435cd16857

import Mathlib

open Finset

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 5000

private def trianglePairOwners : Fin 8 → Fin 5 → Fin 4 :=
  ![![0, 0, 1, 3, 2],
    ![0, 2, 1, 3, 3],
    ![0, 2, 1, 1, 3],
    ![1, 0, 2, 1, 3],
    ![1, 0, 1, 3, 2],
    ![1, 0, 2, 3, 2],
    ![0, 2, 1, 3, 2],
    ![0, 2, 2, 1, 3]]

private theorem trianglePairAssignment :
    ∀ (v : Fin 4) (e f : Fin 5), e ≠ f →
      (v = (![0, 0, 1, 1, 2] : Fin 5 → Fin 4) e ∨
       v = (![1, 2, 2, 3, 3] : Fin 5 → Fin 4) e) →
      (v = (![0, 0, 1, 1, 2] : Fin 5 → Fin 4) f ∨
       v = (![1, 2, 2, 3, 3] : Fin 5 → Fin 4) f) →
      ∃ j : Fin 8,
        (∀ i, trianglePairOwners j i = (![0, 0, 1, 1, 2] : Fin 5 → Fin 4) i ∨
              trianglePairOwners j i = (![1, 2, 2, 3, 3] : Fin 5 → Fin 4) i) ∧
        (∀ i, trianglePairOwners j i = v ↔ i = e ∨ i = f) ∧
        ∀ i i', trianglePairOwners j i = trianglePairOwners j i' →
          trianglePairOwners j i ≠ v → i = i' := by
  decide

/-- On two triangles sharing one edge, all five edges can be covered by
locally admissible retained patterns precisely when one pattern can
cover two of its incident edges. -/
theorem solution (left right : Fin 5 → Fin 4) (posL posR : Fin 5 → ℕ)
    (F : Fin 4 → Finset (Finset ℕ))
    (hleft : left = ![0, 0, 1, 1, 2]) (hright : right = ![1, 2, 2, 3, 3])
    (hF : ∀ v, (F v).Nonempty)
    (hL : ∀ e, ∃ T ∈ F (left e), posL e ∈ T)
    (hR : ∀ e, ∃ T ∈ F (right e), posR e ∈ T) :
    (∃ C : Fin 4 → Finset ℕ, (∀ v, C v ∈ F v) ∧
      ∀ e, posL e ∈ C (left e) ∨ posR e ∈ C (right e)) ↔
    ∃ (v : Fin 4) (e f : Fin 5), e ≠ f ∧
      (v = left e ∨ v = right e) ∧ (v = left f ∨ v = right f) ∧
      ∃ T ∈ F v,
        (if v = left e then posL e else posR e) ∈ T ∧
        (if v = left f then posL f else posR f) ∈ T := by
  classical
  have hdist : ∀ e, left e ≠ right e := by rw [hleft, hright]; decide
  let need (v : Fin 4) (e : Fin 5) := if v = left e then posL e else posR e
  have hNeed (v : Fin 4) (e : Fin 5) (h : v = left e ∨ v = right e) :
      ∃ T ∈ F v, need v e ∈ T := by
    rcases h with h | h
    · subst v
      simpa only [need, if_pos rfl] using hL e
    · subst v
      simpa only [need, if_neg (hdist e).symm] using hR e
  constructor
  · rintro ⟨C, hC, hcover⟩
    let owner (e : Fin 5) := if posL e ∈ C (left e) then left e else right e
    have hmem (e : Fin 5) : (owner e = left e ∨ owner e = right e) ∧
        need (owner e) e ∈ C (owner e) := by
      by_cases hl : posL e ∈ C (left e)
      · simpa only [owner, if_pos hl, need, if_pos rfl, true_or, true_and] using hl
      · have hr := (hcover e).resolve_left hl
        simpa only [owner, if_neg hl, need, if_neg (hdist e).symm, or_true, true_and] using hr
    have hn : ¬ Function.Injective owner := fun h => by
      have hh := Fintype.card_le_of_injective owner h
      simp at hh
    change ¬ (∀ e f : Fin 5, owner e = owner f → e = f) at hn
    push Not at hn
    obtain ⟨e, f, heq, hne⟩ := hn
    exact ⟨owner e, e, f, hne, (hmem e).1, heq.symm ▸ (hmem f).1, C (owner e),
      hC (owner e), (hmem e).2, heq.symm ▸ (hmem f).2⟩
  · rintro ⟨v, e, f, hef, hev, hfv, T, hT, hTe, hTf⟩
    obtain ⟨j, hInc, hV, hInj⟩ := trianglePairAssignment v e f hef
      (by simpa only [← hleft, ← hright] using hev)
      (by simpa only [← hleft, ← hright] using hfv)
    let owner := trianglePairOwners j
    have hh (p : Fin 4) :
        ∃ S ∈ F p, ∀ i, owner i = p → need p i ∈ S := by
      by_cases hp : p = v
      · subst p
        refine ⟨T, hT, ?_⟩
        intro i hi
        rcases (hV i).mp hi with rfl | rfl
        · exact hTe
        · exact hTf
      · by_cases he : ∃ i, owner i = p
        · obtain ⟨i, hi⟩ := he
          have hside : p = left i ∨ p = right i := by
            simpa only [← hleft, ← hright, ← hi] using hInc i
          obtain ⟨S, hS, hn⟩ := hNeed p i hside
          refine ⟨S, hS, fun i' hi' => ?_⟩
          have heq := hInj i' i (hi'.trans hi.symm) (fun hh => hp (hi'.symm.trans hh))
          rw [heq]
          exact hn
        · obtain ⟨S, hS⟩ := hF p
          exact ⟨S, hS, fun i hi => (he ⟨i, hi⟩).elim⟩
    choose C hC hcover using hh
    refine ⟨C, hC, ?_⟩
    intro i
    have hside : owner i = left i ∨ owner i = right i := by
      simpa only [← hleft, ← hright] using hInc i
    rcases hside with hl | hr
    · left
      simpa only [need, if_pos rfl] using hcover (left i) i hl
    · right
      simpa only [need, if_neg (hdist i).symm] using hcover (right i) i hr

