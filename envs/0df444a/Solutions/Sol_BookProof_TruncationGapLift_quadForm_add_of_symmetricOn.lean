-- Prove2me | solution 1 for BookProof.TruncationGapLift.quadForm_add_of_symmetricOn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T13:10:52.569583+00:00
-- url     : https://prove2.me/submissions/1fe78750-9950-4fbe-8ad8-0200e8816219

-- Generated from ChapterTruncationGapLift.lean — solution of BookProof.TruncationGapLift.quadForm_add_of_symmetricOn
import Mathlib
import Definitions.Def_ChapterTruncationGapLift
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterBandEnclosure
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockInteractionStability
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsFockGapChain
import Definitions.Def_ChapterFarisLavineCore
open BookProof.TruncationGapLift



noncomputable section


open BookProof.FarisLavine BookProof.HermiteGalerkin BookProof.BandEnclosure
open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockInteractionStability
open BookProof.YangMillsHermite BookProof.HermiteProductCore
open BookProof.YangMillsFriedrichs BookProof.YangMillsFockGapChain

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution (H : D →ₗ[ℂ] F) (hsym : SymmetricOn D H) (x w : D) :
    quadForm H (x + w) = quadForm H x + quadForm H w
      + 2 * (inner ℂ (x : F) (H w) : ℂ).re := by

  have hcross : (inner ℂ (w : F) (H x) : ℂ).re = (inner ℂ (x : F) (H w) : ℂ).re := by
    have h1 : (inner ℂ (H x) (w : F) : ℂ) = inner ℂ (x : F) (H w) := hsym x w
    have h2 : (inner ℂ (w : F) (H x) : ℂ) = starRingEnd ℂ (inner ℂ (H x) (w : F) : ℂ) :=
      (inner_conj_symm (𝕜 := ℂ) (w : F) (H x)).symm
    rw [h2, h1, Complex.conj_re]
  simp only [quadForm, Submodule.coe_add, map_add, inner_add_left, inner_add_right,
    Complex.add_re]
  rw [hcross]
  ring
