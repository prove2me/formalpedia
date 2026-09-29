-- Prove2me | solution 1 for BraidsLinksMCG.standard_pure_word_eval_conj_v2
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-09-27T23:13:54.00098+00:00
-- url     : https://prove2.me/submissions/35061655-e5da-44cc-80f9-d6b479495d9a

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist
import Definitions.Def_TarchaBraids_generation_word_data_v1
import Definitions.Def_TarchaBraids_standard_pure_braid_word_v1

set_option autoImplicit false

/-!
# Solution for `BraidsLinksMCG.standard_pure_word_eval_conj_v2`

The standard pure braid word is *by construction* a conjugate of the half-twist
square: unfolding `TarchaBraids.standardPureBraidWord` gives

  `σ_{n-1} ⋯ σ_{i+1} ⋅ σ_i^2 ⋅ σ_{n-1}^{-1} ⋯ σ_{i+1}^{-1}`

(in zero-based indexing), i.e. the evaluation of the positive sub-word,
times `σ_i^2`, times its inverse.  No braid relations are needed — only that
`FreeGroup.lift` is a monoid homomorphism and the sign/inverse bookkeeping of
`braidWordFree`.
-/

namespace ConjWordEval

/-- `braidLetterFree` on a positive letter. -/
theorem braidLetterFree_of_sign_pos {n : Nat} (a : TarchaBraids.BraidLetter n)
    (h : a.sign = TarchaBraids.BraidLetterSign.positive) :
    TarchaBraids.braidLetterFree a = FreeGroup.of a.index := by
  rw [show TarchaBraids.braidLetterFree a
      = match a.sign with
        | TarchaBraids.BraidLetterSign.positive => FreeGroup.of a.index
        | TarchaBraids.BraidLetterSign.negative => (FreeGroup.of a.index)⁻¹ from rfl, h]

/-- `braidLetterFree` on a negative letter. -/
theorem braidLetterFree_of_sign_neg {n : Nat} (a : TarchaBraids.BraidLetter n)
    (h : a.sign = TarchaBraids.BraidLetterSign.negative) :
    TarchaBraids.braidLetterFree a = (FreeGroup.of a.index)⁻¹ := by
  rw [show TarchaBraids.braidLetterFree a
      = match a.sign with
        | TarchaBraids.BraidLetterSign.positive => FreeGroup.of a.index
        | TarchaBraids.BraidLetterSign.negative => (FreeGroup.of a.index)⁻¹ from rfl, h]

/-- `braidWordFree` distributes over list append. -/
theorem braidWordFree_append {n : Nat} (l₁ l₂ : List (TarchaBraids.BraidLetter n)) :
    TarchaBraids.braidWordFree (l₁ ++ l₂)
      = TarchaBraids.braidWordFree l₁ * TarchaBraids.braidWordFree l₂ := by
  induction l₁ with
  | nil => simp [TarchaBraids.braidWordFree]
  | cons a t ih =>
    simp only [List.cons_append, TarchaBraids.braidWordFree]
    rw [ih, mul_assoc]

/-- A negative-signed word is the inverse of the reversed positive-signed word. -/
theorem braidWordFree_map_neg_rev {m : Nat} (l : List (Fin m))
    (pos neg : Fin m → TarchaBraids.BraidLetter (m + 1))
    (hpsign : ∀ k, (pos k).sign = TarchaBraids.BraidLetterSign.positive)
    (hnsign : ∀ k, (neg k).sign = TarchaBraids.BraidLetterSign.negative)
    (hidx : ∀ k, (neg k).index = (pos k).index) :
    TarchaBraids.braidWordFree (l.map neg)
      = (TarchaBraids.braidWordFree (l.reverse.map pos))⁻¹ := by
  induction l with
  | nil => simp [TarchaBraids.braidWordFree]
  | cons k t ih =>
    have e1 : TarchaBraids.braidLetterFree (neg k) = (FreeGroup.of (pos k).index)⁻¹ := by
      rw [braidLetterFree_of_sign_neg _ (hnsign k), hidx k]
    have e2 : TarchaBraids.braidLetterFree (pos k) = FreeGroup.of (pos k).index :=
      braidLetterFree_of_sign_pos _ (hpsign k)
    have s1 : TarchaBraids.braidWordFree ((k :: t).map neg)
        = TarchaBraids.braidLetterFree (neg k) * TarchaBraids.braidWordFree (t.map neg) := by
      simp [TarchaBraids.braidWordFree]
    have s2 : TarchaBraids.braidLetterFree (pos k)
        = TarchaBraids.braidWordFree [pos k] := by
      simp [TarchaBraids.braidWordFree]
    have r1 : (k :: t).reverse.map pos = t.reverse.map pos ++ [pos k] := by
      simp [List.reverse_cons]
    rw [s1, e1, ih, ← mul_inv_rev, ← e2, s2, ← braidWordFree_append, r1]

end ConjWordEval

theorem solution (n : Nat) (i : Fin (n + 1)) :
    ∃ c : BraidsLinksMCG.GeomBraidGroup (n + 2),
      FreeGroup.lift (fun j : Fin (n + 2 - 1) => TarchaBraids.halfTwistBraid (n + 2) j)
        (TarchaBraids.braidWordFree (TarchaBraids.standardPureBraidWord (n + 1) i))
        = c * (TarchaBraids.halfTwistBraid (n + 2) i) ^ 2 * c⁻¹ := by
  set f : Fin (n + 2 - 1) → BraidsLinksMCG.GeomBraidGroup (n + 2) :=
    fun j => TarchaBraids.halfTwistBraid (n + 2) j with hf
  set higher : List (Fin (n + 1)) :=
    (List.finRange (n + 1)).filter (fun k => i < k) with hh
  set pos : Fin (n + 1) → TarchaBraids.BraidLetter (n + 2) :=
    fun k => { index := Fin.cast (by omega) k
             , sign := TarchaBraids.BraidLetterSign.positive } with hpos
  set neg : Fin (n + 1) → TarchaBraids.BraidLetter (n + 2) :=
    fun k => { index := Fin.cast (by omega) k
             , sign := TarchaBraids.BraidLetterSign.negative } with hneg
  have hword : TarchaBraids.standardPureBraidWord (n + 1) i
      = higher.reverse.map pos ++ [pos i, pos i] ++ higher.map neg := rfl
  have key : TarchaBraids.braidWordFree (higher.map neg)
      = (TarchaBraids.braidWordFree (higher.reverse.map pos))⁻¹ :=
    ConjWordEval.braidWordFree_map_neg_rev higher pos neg
      (by intro k; rfl) (by intro k; rfl) (by intro k; rfl)
  have eM : FreeGroup.lift f (TarchaBraids.braidWordFree [pos i, pos i])
      = (TarchaBraids.halfTwistBraid (n + 2) i) ^ 2 := by
    have e1 : TarchaBraids.braidLetterFree (pos i) = FreeGroup.of (pos i).index :=
      ConjWordEval.braidLetterFree_of_sign_pos _ rfl
    have e3 : f (pos i).index = TarchaBraids.halfTwistBraid (n + 2) i := by
      have hc : (pos i).index = i := Fin.ext rfl
      rw [hc]
    rw [show TarchaBraids.braidWordFree [pos i, pos i]
        = TarchaBraids.braidLetterFree (pos i) * TarchaBraids.braidLetterFree (pos i) from by
          simp [TarchaBraids.braidWordFree],
      map_mul, e1, FreeGroup.lift_apply_of, e3, ← pow_two]
  refine ⟨FreeGroup.lift f (TarchaBraids.braidWordFree (higher.reverse.map pos)), ?_⟩
  rw [hword, ConjWordEval.braidWordFree_append, ConjWordEval.braidWordFree_append,
    map_mul, map_mul, key, map_inv, eM, mul_assoc]
