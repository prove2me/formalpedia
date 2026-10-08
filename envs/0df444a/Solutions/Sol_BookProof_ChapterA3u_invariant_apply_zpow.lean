-- Prove2me | solution 1 for BookProof.ChapterA3u.invariant_apply_zpow
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T05:32:21.719875+00:00
-- url     : https://prove2.me/submissions/5e32a40a-149f-4e41-b862-ae0e375e59a9

-- Generated from ChapterA3u.lean — theorem BookProof.ChapterA3u.invariant_apply_zpow
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
    (ha : a ∘ σ = a) (k : ℤ) (x : Fin N) : a ((σ ^ k) x) = a x := by
  cases k with
  | ofNat n => simpa using invariant_pow ha n x
  | negSucc n =>
    have hinv : a ∘ (σ⁻¹ : Equiv.Perm (Fin N)) = a := by
      funext y
      have hh := congrFun ha (σ⁻¹ y)
      simpa using hh.symm
    simpa only [zpow_negSucc, ← inv_pow] using invariant_pow hinv (n + 1) x

#print axioms solution
