-- Prove2me | solution 1 for BhangaleHypergraph.Main.outer_completeness
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:46:00.334167+00:00
-- url     : https://prove2.me/submissions/52d2fc5b-16b4-455f-a2c9-0f92cc02272f

import Definitions.Def_BhangaleHypergraph_Main_Base

open BhangaleHypergraph.Main

private lemma inBall_mono (B : BaseCover) {r s : ℕ} {a : Fin B.A} {v : BaseVertex B}
    (h : InBall B r a v) (hrs : r ≤ s) : InBall B s a v := by
  obtain ⟨k, hkr, walk, hzero, hlast, hadj⟩ := h
  exact ⟨k, hkr.trans hrs, walk, hzero, hlast, hadj⟩

private lemma inBall_prepend_two (B : BaseCover) {r : ℕ} {c a : Fin B.A}
    (u v : BaseVertex B) (h : InBall B r a v)
    (hcu : BaseAdjacent B (.inl c) u) (hua : BaseAdjacent B u (.inl a)) :
    InBall B (r + 2) c v := by
  obtain ⟨k, hkr, walk, hzero, hlast, hadj⟩ := h
  refine ⟨k + 2, by omega, Fin.cons (.inl c) (Fin.cons u walk), ?_, ?_, ?_⟩
  · simp
  · simpa using hlast
  · intro j
    refine Fin.cases ?_ (fun q => ?_) j
    · simpa using hcu
    · refine Fin.cases ?_ (fun p => ?_) q
      · have h1 : (1 : Fin (k + 3)) = (0 : Fin (k + 2)).succ := by
          ext
          simp
        have h2 : (2 : Fin (k + 3)) = (1 : Fin (k + 2)).succ := by
          ext
          simp
        have h1' : (1 : Fin (k + 2)) = (0 : Fin (k + 1)).succ := by
          ext
          simp
        simp only [h1, h2, Fin.cons_succ, Fin.cons_zero, h1', hzero]
        exact hua
      · simpa using hadj p

private lemma radius_add_two_le {ell : ℕ} {i j : Fin ell} (hij : i < j) :
    Radius ell j + 2 ≤ Radius ell i := by
  unfold Radius
  omega

theorem solution (B : BaseCover) (ell : ℕ) (hell : 2 ≤ ell)
    (hsat : BaseSatisfiable B) :
    ∃ σ : NeighborhoodLabeling B ell,
      ∀ (i j : Fin ell), i < j → ∀ e e' : Fin B.E, B.right e = B.right e' →
        RestrictionSatisfied B σ i j e e' := by
  classical
  obtain ⟨τ, hτ⟩ := hsat
  let chunk (i : Fin ell) (a : Fin B.A) : LocalAssignment B (Radius ell i) a :=
    ⟨fun v => if InBall B (Radius ell i) a v then τ v else ⟨0, BaseAlphabetPositive B v⟩, by
      constructor
      · intro v hv
        simp [hv]
      · intro e heL heR
        simp [heL, heR]
        exact hτ e⟩
  refine ⟨chunk, ?_⟩
  intro i j hij e e' hrr v hv
  have htwo : InBall B (Radius ell j + 2) (B.left e) v := by
    apply inBall_prepend_two B (.inr (B.right e)) v hv
    · exact ⟨e, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨e', Or.inr ⟨rfl, congrArg Sum.inr hrr⟩⟩
  have hball : InBall B (Radius ell i) (B.left e) v :=
    inBall_mono B htwo (radius_add_two_le hij)
  simp [chunk, hball, hv]
