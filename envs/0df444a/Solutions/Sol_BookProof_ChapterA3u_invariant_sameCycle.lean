-- Prove2me | solution 1 for BookProof.ChapterA3u.invariant_sameCycle
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T05:30:14.730999+00:00
-- url     : https://prove2.me/submissions/a461db9e-4394-4007-9c66-7cde31b28bf7

-- Generated from ChapterA3u.lean — theorem BookProof.ChapterA3u.invariant_sameCycle
import Definitions.Def_ChapterA3o
import Definitions.Def_ChapterA3q
import Definitions.Def_ChapterA3r
import Mathlib
import Definitions.Def_ChapterA3u
import Definitions.Def_ChapterA3n
open BookProof.ChapterA3n
open BookProof.ChapterA3u


open Matrix
open scoped BigOperators


open BookProof.ChapterA3n BookProof.ChapterA3o BookProof.ChapterA3q
open BookProof.ChapterA3r

private theorem invariant_pow {N : ℕ} {σ : Equiv.Perm (Fin N)} {a : Idx N}
    (ha : a ∘ σ = a) (n : ℕ) (x : Fin N) : a ((σ ^ n) x) = a x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Equiv.Perm.mul_apply, ih]
    exact congrFun ha x

theorem solution {N : ℕ} {σ : Equiv.Perm (Fin N)} {a : Idx N}
    (ha : a ∘ σ = a) {x y : Fin N} (h : σ.SameCycle x y) : a x = a y := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  rw [← hn]
  exact (invariant_pow ha n x).symm

#print axioms solution

