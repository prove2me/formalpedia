-- Prove2me | solution 2 for BookProof.TruncationGapLift.gap_of_level_gap_and_tail
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T12:21:52.87717+00:00
-- url     : https://prove2.me/submissions/47cbebcd-0fb2-4897-9d48-9c5029f2874b

-- Generated from ChapterTruncationGapLift.lean — solution of BookProof.TruncationGapLift.gap_of_level_gap_and_tail
import Mathlib
import Definitions.Def_ChapterTruncationGapLift
import Theorems.Thm_BookProof_TruncationGapLift_norm_add_sq_of_galerkin_tail
import Theorems.Thm_BookProof_TruncationGapLift_exists_galerkin_tail_decomp
import Theorems.Thm_BookProof_TruncationGapLift_quadForm_add_of_symmetricOn
import Theorems.Thm_BookProof_HermiteGalerkin_galerkinSpan_le_finiteModeDomain
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
    (H : finiteModeDomain b →ₗ[ℂ] F) (hsym : SymmetricOn _ H) {m : ℕ} {mu eps : ℝ}
    (heps : 0 ≤ eps)
    (htrunc : ∀ x : finiteModeDomain b, (x : F) ∈ galerkinSpan b m →
      mu * ‖(x : F)‖ ^ 2 ≤ quadForm H x)
    (htail : ∀ w : finiteModeDomain b, (w : F) ∈ tailSpan b m →
      mu * ‖(w : F)‖ ^ 2 ≤ quadForm H w)
    (hcoup : ∀ x w : finiteModeDomain b, (x : F) ∈ galerkinSpan b m →
      (w : F) ∈ tailSpan b m →
      |(inner ℂ (x : F) (H w) : ℂ).re| ≤ eps * ‖(x : F)‖ * ‖(w : F)‖)
    (v : finiteModeDomain b) : (mu - eps) * ‖(v : F)‖ ^ 2 ≤ quadForm H v := by

  obtain ⟨x, hx, w, hw, hxw⟩ := exists_galerkin_tail_decomp b m v.2
  let X : finiteModeDomain b := ⟨x, galerkinSpan_le_finiteModeDomain b m hx⟩
  let W : finiteModeDomain b := ⟨w, tailSpan_le_finiteModeDomain b m hw⟩
  have hXc : (X : F) = x := rfl
  have hWc : (W : F) = w := rfl
  have hv : v = X + W := Subtype.ext (by simpa [hXc, hWc] using hxw)
  have hqv : quadForm H v
      = quadForm H X + quadForm H W + 2 * (inner ℂ (X : F) (H W) : ℂ).re := by
    rw [hv]; exact quadForm_add_of_symmetricOn H hsym X W
  have hnorm : ‖(v : F)‖ ^ 2 = ‖x‖ ^ 2 + ‖w‖ ^ 2 := by
    rw [hxw]; exact norm_add_sq_of_galerkin_tail b hx hw
  have h1 : mu * ‖x‖ ^ 2 ≤ quadForm H X := htrunc X hx
  have h2 : mu * ‖w‖ ^ 2 ≤ quadForm H W := htail W hw
  have h3 : |(inner ℂ (X : F) (H W) : ℂ).re| ≤ eps * ‖x‖ * ‖w‖ := hcoup X W hx hw
  have hcross : -(eps * ‖x‖ * ‖w‖) ≤ (inner ℂ (X : F) (H W) : ℂ).re := (abs_le.mp h3).1
  have hsq : 0 ≤ eps * (‖x‖ - ‖w‖) ^ 2 := mul_nonneg heps (sq_nonneg _)
  rw [hqv, hnorm]
  nlinarith [hsq, hcross, h1, h2]
