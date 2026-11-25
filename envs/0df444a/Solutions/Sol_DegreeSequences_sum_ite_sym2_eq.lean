-- Prove2me | solution 1 for DegreeSequences.sum_ite_sym2_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T14:56:56.173084+00:00
-- url     : https://prove2.me/submissions/b3cdedb7-2123-4dde-a5ca-2a24e77507f5

module
public import Mathlib
public import Definitions.Def_DegreeSeqLib_DegreeSequences

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open DegreeSequences
namespace DegreeSequences
theorem _root_.solution {V : Type*} [Fintype V] [DecidableEq V] (v : V) (e : Sym2 V)
    (he : ¬ e.IsDiag) :
    (∑ w, if s(v, w) = e then 1 else 0) = if v ∈ e then 1 else 0 := by
  induction e using Sym2.ind with
  | _ a b =>
  have hab : a ≠ b := by simpa using he
  by_cases hva : v = a
  · subst hva
    rw [Finset.sum_eq_single b]
    · simp
    · intro w _ hw
      simp [hw, hab]
    · simp
  by_cases hvb : v = b
  · subst hvb
    rw [Finset.sum_eq_single a]
    · simp [Sym2.eq_swap]
    · intro w _ hw
      simp [hw, hva]
    · simp
  · rw [Finset.sum_eq_zero]
    · simp [hva, hvb]
    · intro w _
      simp [hva, hvb]
end DegreeSequences
