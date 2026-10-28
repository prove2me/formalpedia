-- Prove2me | solution 1 for BookProof.NavierStokesFlow.DiagonalEsa.diagOp_hasZeroDeficiencyOn
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-22T05:34:46.374859+00:00
-- url     : https://prove2.me/submissions/0b6e0718-e0ec-479c-9156-e8269fcbb48d

import Mathlib
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterAbelianDiagonalCountable
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.ChapterAbelianDiagonalCountable
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.DiagonalEsa


open scoped ENNReal

theorem dgz_key (c : ℕ → ℝ) (w : lp (fun _ : ℕ => ℂ) 2) (s : ℂ) (hs : ∀ k : ℕ, (c k : ℂ) ≠ s)
    (hw : ∀ v : lpFiniteModes ℕ,
      (inner ℂ ((DiagonalEsa.diagOp c v : lpFiniteModes ℕ) : lp (fun _ : ℕ => ℂ) 2) w : ℂ)
        = inner ℂ ((v : lpFiniteModes ℕ) : lp (fun _ : ℕ => ℂ) 2) (s • w)) : w = 0 := by
  ext k
  have h := hw (DiagonalEsa.basis k)
  have hd : ((DiagonalEsa.diagOp c (DiagonalEsa.basis k) : lpFiniteModes ℕ) : lp (fun _ : ℕ => ℂ) 2)
      = lp.single 2 k ((c k : ℂ)) := by
    ext n
    rw [DiagonalEsa.diagOp_coe]
    simp only [DiagonalEsa.diagFun, DiagonalEsa.basis, lp.single_apply, Pi.single_apply]
    split_ifs with hn
    · subst hn; simp
    · simp
  rw [hd] at h
  change (inner ℂ (lp.single 2 k ((c k : ℂ))) w : ℂ) = inner ℂ (lp.single 2 k (1 : ℂ)) (s • w) at h
  rw [lp.inner_single_left, lp.inner_single_left] at h
  simp only [RCLike.inner_apply, Complex.conj_ofReal, map_one, one_mul, lp.coeFn_smul,
    Pi.smul_apply, smul_eq_mul] at h
  have h2 : ((c k : ℂ) - s) * w k = 0 := by
    have : w k * (c k : ℂ) = s * w k := by simpa [mul_comm] using h
    linear_combination this
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd (sub_eq_zero.mp h3) (hs k)
  · simpa using h3

theorem solution (c : ℕ → ℝ) :
    HasZeroDeficiencyOn (lpFiniteModes ℕ) (DiagonalEsa.diagOp c) := by
  constructor
  · intro w hw
    refine dgz_key c w Complex.I (fun k h => by simpa using congrArg Complex.im h) hw
  · intro w hw
    refine dgz_key c w (-Complex.I) (fun k h => by simpa using congrArg Complex.im h) ?_
    intro v; rw [hw v, neg_smul]
