-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.exists_hole_tail_le_compressionLengthBoundIter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:08:18.339628+00:00
-- url     : https://prove2.me/submissions/39a81d58-0978-4fc7-aada-26bec4f5a2ef

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Bound
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Transport
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_RunCovers
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Compression
public import Theorems.Thm_DeciSigma1_Holes_Tail_exists_hole_compressed_step
public import Theorems.Thm_DeciSigma1_Holes_Tail_tail_le_of_empty
public import Theorems.Thm_DeciSigma1_Holes_Tail_le_compressionLengthBoundIter
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_trans


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Holes.Periodic DeciSigma1.Readers DeciSigma1.Words
variable {α S : Type} {k : ℕ}
variable [DecidableEq α] [Fintype S] [DecidableEq S]
namespace DeciSigma1.Holes.Tail
theorem _root_.solution (M : StructuralReader α S k) (D : ℕ)
    (n : ℕ) : ∀ (U : Fin k → List α) (E : ℕ),
    M.IsHole U → HasBoundedRunCover M U n D E →
    ∃ U', M.IsHole U' ∧ ∀ i, M.Immortal (M.endState U' i) → M.rejectedTailLength U' i ≤
      compressionLengthBoundIter k (Fintype.card S) D n E := by
  induction n with
  | zero =>
    rintro U E hU ⟨runs, hcard, -, hE⟩
    have : runs = ∅ := Finset.card_eq_zero.mp (by omega)
    subst this
    exact ⟨U, hU, fun i hi => tail_le_of_empty M hE i hi⟩
  | succ n ih =>
    rintro U E hU ⟨runs, hcard, hruns, hE⟩
    by_cases hne : runs.Nonempty
    · obtain ⟨U', hU', hcov⟩ := exists_hole_compressed_step M hU runs hcard hruns hE hne
      exact ih U' _ hU' hcov
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      subst hne
      exact ⟨U, hU, fun i hi =>
        (tail_le_of_empty M hE i hi).trans (le_compressionLengthBoundIter _ _ _ _ _)⟩
end DeciSigma1.Holes.Tail
