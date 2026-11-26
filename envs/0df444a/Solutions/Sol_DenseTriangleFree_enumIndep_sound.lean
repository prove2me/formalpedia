-- Prove2me | solution 1 for DenseTriangleFree.enumIndep_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:47:14.324272+00:00
-- url     : https://prove2.me/submissions/a6f8321f-ee10-4358-a042-b4d7c3039bd9

module
public import Mathlib
public import Definitions.Def_JinLib_Grotzsch
public import Definitions.Def_JinLib_Heavy

set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
open SimpleGraph
namespace DenseTriangleFree
theorem _root_.solution (E : ℕ → ℕ → Bool) (P : List ℕ → Bool)
    (hP : ∀ l l' : List ℕ, l.Perm l' → P l = P l') (q : ℕ → Prop) [DecidablePred q]
    (hq : ∀ i j, q i → q j → E i j = false) :
    ∀ vs ch : List ℕ, (∀ j ∈ ch, q j) → enumIndep E P vs ch = true →
      P (vs.filter (fun i => decide (q i)) ++ ch) = true := by
  intro vs
  induction vs with
  | nil => intro ch _ h; simpa [enumIndep] using h
  | cons v vs ih =>
    intro ch hch h
    simp only [enumIndep, Bool.and_eq_true, Bool.or_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    by_cases hv : q v
    · have hany : ch.any (E v) = false := by
        rw [List.any_eq_false]
        intro j hj
        simp [hq v j hv (hch j hj)]
      rcases h2 with h2 | h2
      · rw [hany] at h2; exact absurd h2 (by simp)
      have := ih (v :: ch) (by
        intro j hj
        rcases List.mem_cons.mp hj with rfl | hj
        · exact hv
        · exact hch j hj) h2
      rw [List.filter_cons_of_pos (by simpa using hv)]
      rw [List.cons_append, ← hP _ _ List.perm_middle]
      exact this
    · rw [List.filter_cons_of_neg (by simpa using hv)]
      exact ih ch hch h1
end DenseTriangleFree
