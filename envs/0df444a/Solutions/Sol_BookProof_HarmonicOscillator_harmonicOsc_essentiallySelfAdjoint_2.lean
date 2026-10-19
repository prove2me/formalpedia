-- Prove2me | solution 2 for BookProof.HarmonicOscillator.harmonicOsc_essentiallySelfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T07:50:21.384782+00:00
-- url     : https://prove2.me/submissions/8b48a15e-01f2-4574-bad0-76fd492f90d8

import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterStrichartzHermiteQG
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterHarmonicOscillatorEsa
import Definitions.Def_ChapterFarisLavineCore
import Theorems.Thm_BookProof_HermiteStrichartzQG_hermiteCoreOp_hermiteLp
import Theorems.Thm_BookProof_HermiteStrichartzQG_hermiteCore_dense
-- Generated from ChapterHarmonicOscillatorEsa.lean — theorem BookProof.HarmonicOscillator.harmonicOsc_essentiallySelfAdjoint
open BookProof.HarmonicOscillator



open MeasureTheory Polynomial BookProof.HermiteCore BookProof.HermiteStrichartzQG
open BookProof.FarisLavine
theorem h44_hermDef (lam : ℕ → ℝ) (z : ℂ) (hz : ∀ n, (lam n : ℂ) ≠ z) :
    DeficiencyTrivialAt hermiteCore (hermiteCoreOp lam) z := by
  intro w hw
  have hgen : ∀ n, inner ℂ (hermiteLp n) w = 0 := by
    intro n
    have h1 := hw ⟨hermiteLp n, BookProof.HermiteStrichartzQG.hermiteLp_mem_hermiteCore n⟩
    rw [BookProof.HermiteStrichartzQG.hermiteCoreOp_hermiteLp, inner_smul_left,
      Complex.conj_ofReal] at h1
    have h2 : ((lam n : ℂ) - z) * inner ℂ (hermiteLp n) w = 0 := by
      rw [sub_mul, h1]; simp
    exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr (hz n))
  apply BookProof.HermiteStrichartzQG.hermiteCore_dense.eq_zero_of_inner_right ℂ
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => obtain ⟨n, rfl⟩ := hx; exact hgen n
  | zero => simp
  | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
  | smul a x _ hx => rw [inner_smul_left, hx, mul_zero]

theorem solution :
    EssentiallySelfAdjointOn hermiteCore harmonicOscOp := by
  constructor
  · apply h44_hermDef
    intro n h
    have := congrArg Complex.im h
    simp at this
  · apply h44_hermDef
    intro n h
    have := congrArg Complex.im h
    simp at this

