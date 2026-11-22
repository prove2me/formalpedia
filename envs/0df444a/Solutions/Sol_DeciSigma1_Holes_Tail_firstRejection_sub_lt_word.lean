-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.firstRejection_sub_lt_word
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:55:08.544697+00:00
-- url     : https://prove2.me/submissions/e5702e42-d2db-4ea1-ba2f-4c1fe9aa5dcf

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ClosedFactors
public import Mathlib.Order.Nat
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Levels
public import Theorems.Thm_DeciSigma1_Holes_Tail_no_early_repeat
public import Theorems.Thm_DeciSigma1_Holes_Periodic_FollowerEdge_symm
public import Theorems.Thm_DeciSigma1_Readers_StructuralReader_firstRejection_spec
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_symm
public import Theorems.Thm_DeciSigma1_Words_PeriodicFrom_add_mul
public import Theorems.Thm_DeciSigma1_Words_PeriodicOn_eq_of_le_add


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Holes.Periodic DeciSigma1.Readers DeciSigma1.Words
variable {α S : Type} {k : ℕ}
variable {M : StructuralReader α S k} {W : Fin k → List α} {i : Fin k}
namespace DeciSigma1.Holes.Tail
theorem _root_.solution [Fintype S] (h : M.Eligible W i) {p s e : ℕ} (hp : 0 < p)
    (hper : PeriodicOn (W i) p s e) (hsJ : s ≤ M.firstRejection W i)
        (hJe : M.firstRejection W i ≤ e) :
    M.firstRejection W i - s < Fintype.card S * p := by
  classical
  by_contra hge
  push Not at hge
  obtain ⟨hJl, hJr, hJb⟩ := StructuralReader.firstRejection_spec h
  have hcut : ∀ j : Fin (Fintype.card S), s + j * p < M.firstRejection W i := by
    intro j
    have : (j : ℕ) * p < Fintype.card S * p := Nat.mul_lt_mul_of_pos_right j.isLt hp
    omega
  let f : Fin (Fintype.card S) → {q : S // M.rejected q = false} :=
    fun j => ⟨M.runPrefix W i (s + j * p), hJb _ (hcut j)⟩
  have hcard : Fintype.card {q : S // M.rejected q = false} <
      Fintype.card (Fin (Fintype.card S)) := by
    rw [Fintype.card_fin]
    exact Fintype.card_subtype_lt (p := fun q => M.rejected q = false)
        (x := M.runPrefix W i (M.firstRejection W i))
      (by rw [hJr]; decide)
  obtain ⟨j₁, j₂, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  have hq : M.runPrefix W i (s + j₁ * p) = M.runPrefix W i (s + j₂ * p) := congrArg Subtype.val heq
  have key : ∀ a b : Fin (Fintype.card S), (a : ℕ) < b →
      M.runPrefix W i (s + a * p) = M.runPrefix W i (s + b * p) → False := by
    intro a b hab hq'
    have hm : (a : ℕ) * p < b * p := Nat.mul_lt_mul_of_pos_right hab hp
    have hsplit : ((b : ℕ) - a) * p + a * p = b * p := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hab.le]
    apply no_early_repeat h (a' := s + a * p) (a := s + b * p) (by omega) (hcut b).le _ hq'
    intro t ht
    have := hper.eq_of_le_add (p := s + a * p + t) (by omega) ((b : ℕ) - a) (by omega)
    rw [this]; congr 1; omega
  rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
  · exact key j₁ j₂ hlt hq
  · exact key j₂ j₁ hlt hq.symm
end DeciSigma1.Holes.Tail
