-- Prove2me | solution 1 for BookProof.DirectSumEsa.essentiallySelfAdjointOn_of_hasZeroDeficiencyOn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T05:49:59.051423+00:00
-- url     : https://prove2.me/submissions/3c539634-fbad-4a62-b058-ab4d8e4149e7

-- Generated from ChapterDirectSumEsa.lean — solution of BookProof.DirectSumEsa.essentiallySelfAdjointOn_of_hasZeroDeficiencyOn
import Mathlib
import Definitions.Def_ChapterDirectSumEsa
open BookProof.DirectSumEsa



open scoped ENNReal


open BookProof.FarisLavine

noncomputable section

variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)]
open BookProof.NavierStokesFlow

variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)]
variable {D : ∀ i, Submodule ℂ (G i)}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

set_option maxHeartbeats 1000000 in
theorem solution {Dom : Submodule ℂ F}
    (A : Dom →ₗ[ℂ] Dom) (h : HasZeroDeficiencyOn Dom A) :
    EssentiallySelfAdjointOn Dom (Dom.subtype.comp A) := by

  constructor
  · intro w hw
    refine h.1 w (fun v => ?_)
    have hv : (inner ℂ (((Dom.subtype.comp A) v : F)) w : ℂ)
        = Complex.I * inner ℂ ((v : F)) w := hw v
    rw [inner_smul_right]
    exact hv
  · intro w hw
    refine h.2 w (fun v => ?_)
    have hv : (inner ℂ (((Dom.subtype.comp A) v : F)) w : ℂ)
        = -Complex.I * inner ℂ ((v : F)) w := hw v
    rw [inner_neg_right, inner_smul_right]
    exact hv.trans (by ring)
