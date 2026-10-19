-- Prove2me | solution 1 for BookProof.NavierStokesFlow.DiagonalEsa.diagOp_not_bounded
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T03:25:55.793757+00:00
-- url     : https://prove2.me/submissions/d3c06c28-3631-4826-a49e-722b1257c76b

import Mathlib
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterAbelianDiagonalCountable
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
-- Generated from ChapterNavierStokesDeficiency.lean — theorem BookProof.NavierStokesFlow.DiagonalEsa.diagOp_not_bounded
open BookProof.ChapterAbelianDiagonalCountable
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.DiagonalEsa


open scoped ENNReal
theorem h43_diagOp_basis (c : ℕ → ℝ) (n : ℕ) : diagOp c (basis n) = ((c n : ℂ)) • basis n := by
  apply Subtype.ext
  ext k
  show diagFun c _ k = _
  simp only [diagFun, basis, Submodule.coe_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  by_cases h : k = n
  · subst h; simp
  · simp [lp.single_apply, h]

theorem h43_norm_basis (n : ℕ) : ‖basis n‖ = 1 := by
  show ‖(lp.single 2 n (1:ℂ) : lp (fun _ : ℕ => ℂ) 2)‖ = 1
  rw [lp.norm_single (by norm_num)]; simp

theorem solution (c : ℕ → ℝ) (hc : ∀ C : ℝ, ∃ n, C < |c n|) :
    ¬ ∃ C : ℝ, ∀ f : lpFiniteModes ℕ, ‖diagOp c f‖ ≤ C * ‖f‖ := by
  rintro ⟨C, hC⟩
  obtain ⟨n, hn⟩ := hc C
  have := hC (basis n)
  rw [h43_diagOp_basis, norm_smul, h43_norm_basis] at this
  simp at this
  linarith

