-- Prove2me | solution 1 for BookProof.TruncationGapLift.gap_of_level_gap_and_tail_decoupled
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T13:18:15.381261+00:00
-- url     : https://prove2.me/submissions/98f0b6f6-ed6a-4d97-9923-11ff567b9962

-- Generated from ChapterTruncationGapLift.lean — solution of BookProof.TruncationGapLift.gap_of_level_gap_and_tail_decoupled
import Mathlib
import Definitions.Def_ChapterTruncationGapLift
import Theorems.Thm_BookProof_TruncationGapLift_gap_of_level_gap_and_tail
import Definitions.Def_ChapterFarisLavine
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
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
open BookProof.TruncationGapLift



noncomputable section


open BookProof.FarisLavine BookProof.HermiteGalerkin BookProof.BandEnclosure
open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockInteractionStability
open BookProof.YangMillsHermite BookProof.HermiteProductCore
open BookProof.YangMillsFriedrichs BookProof.YangMillsFockGapChain
open BookProof.HermiteGalerkin

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution (b : HilbertBasis ℕ ℂ F)
    (H : finiteModeDomain b →ₗ[ℂ] F) (hsym : SymmetricOn _ H) {m : ℕ} {mu : ℝ}
    (htrunc : ∀ x : finiteModeDomain b, (x : F) ∈ galerkinSpan b m →
      mu * ‖(x : F)‖ ^ 2 ≤ quadForm H x)
    (htail : ∀ w : finiteModeDomain b, (w : F) ∈ tailSpan b m →
      mu * ‖(w : F)‖ ^ 2 ≤ quadForm H w)
    (hdec : ∀ x w : finiteModeDomain b, (x : F) ∈ galerkinSpan b m →
      (w : F) ∈ tailSpan b m → (inner ℂ (x : F) (H w) : ℂ).re = 0)
    (v : finiteModeDomain b) : mu * ‖(v : F)‖ ^ 2 ≤ quadForm H v := by

  have h := gap_of_level_gap_and_tail (eps := 0) b H hsym le_rfl htrunc htail
    (by intro x w hx hw; simp [hdec x w hx hw]) v
  simpa using h
