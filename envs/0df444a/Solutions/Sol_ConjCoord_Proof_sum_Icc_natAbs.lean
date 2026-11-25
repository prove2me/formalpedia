-- Prove2me | solution 1 for ConjCoord.Proof.sum_Icc_natAbs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:47:08.127812+00:00
-- url     : https://prove2.me/submissions/259fa349-0400-4509-9ddd-098a7a4f5403

module
public import Definitions.Def_ConjCoord_Defs
public import Definitions.Def_ConjCoord_Compute

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof
namespace ConjCoord.Proof
theorem _root_.solution {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ∑ x ∈ Icc (-(n : ℤ)) n, f x.natAbs = ∑ k ∈ range (n + 1), wt k • f k := by
  induction n with
  | zero => simp [wt]
  | succ n ih =>
    have hset : Icc (-((n + 1 : ℕ) : ℤ)) ((n + 1 : ℕ) : ℤ) =
        insert ((n : ℤ) + 1) (insert (-((n : ℤ) + 1)) (Icc (-(n : ℤ)) n)) := by
      ext x; simp only [mem_Icc, mem_insert]; push_cast; omega
    rw [hset, sum_insert (by simp only [mem_insert, mem_Icc]; omega),
      sum_insert (by simp only [mem_Icc]; omega), ih,
      sum_range_succ (fun k => wt k • f k) (n + 1)]
    have h1 : ((n : ℤ) + 1).natAbs = n + 1 := by omega
    have h2 : (-((n : ℤ) + 1)).natAbs = n + 1 := by omega
    have hw : wt (n + 1) = 2 := by simp [wt]
    rw [h1, h2, hw, two_smul]; abel
end ConjCoord.Proof
