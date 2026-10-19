-- Prove2me | solution 1 for BookProof.TruncationGapLift.quadForm_ge_of_le_ritzInf_on
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T07:24:42.438183+00:00
-- url     : https://prove2.me/submissions/624fc308-83bb-46cf-9532-9fc1b37996ef

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
import Mathlib
import Definitions.Def_ChapterTruncationGapLift
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
-- Generated from ChapterTruncationGapLift.lean — theorem BookProof.TruncationGapLift.quadForm_ge_of_le_ritzInf_on
open BookProof.HermiteGalerkin
open BookProof.TruncationGapLift


noncomputable section


open BookProof.FarisLavine BookProof.HermiteGalerkin BookProof.BandEnclosure
open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockInteractionStability
open BookProof.YangMillsHermite BookProof.HermiteProductCore
open BookProof.YangMillsFriedrichs BookProof.YangMillsFockGapChain

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

variable {D : Submodule ℂ F}
theorem h44_qf_ge {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
    (H : D →ₗ[ℂ] F)
    (hpos : ∀ x : D, 0 ≤ BookProof.FarisLavine.quadForm H x) {V : Submodule ℂ F} {mu : ℝ}
    (hmu : mu ≤ BookProof.HermiteGalerkin.ritzInf H V) (x : D) (hx : (x : F) ∈ V) :
    mu * ‖(x : F)‖ ^ 2 ≤ BookProof.FarisLavine.quadForm H x := by
  by_cases h0 : (x : F) = 0
  · rw [h0, norm_zero]; simpa using hpos x
  have hn : 0 < ‖(x : F)‖ := norm_pos_iff.mpr h0
  set c : ℝ := ‖(x : F)‖⁻¹ with hc
  let y : D := (c : ℂ) • x
  have hyF : (y : F) = (c : ℂ) • (x : F) := rfl
  have hyV : (y : F) ∈ V := by rw [hyF]; exact V.smul_mem _ hx
  have hy1 : ‖(y : F)‖ = 1 := by
    rw [hyF, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)]
    exact inv_mul_cancel₀ hn.ne'
  have hqy : BookProof.FarisLavine.quadForm H y = c ^ 2 * BookProof.FarisLavine.quadForm H x := by
    unfold BookProof.FarisLavine.quadForm
    rw [hyF, map_smul, inner_smul_left, inner_smul_right]
    simp only [Complex.conj_ofReal]
    rw [← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul]; ring
  have hmem : BookProof.FarisLavine.quadForm H y ∈ BookProof.HermiteGalerkin.ritzSet H V :=
    ⟨y, hyV, hy1, rfl⟩
  have hbdd : BddBelow (BookProof.HermiteGalerkin.ritzSet H V) :=
    ⟨0, by rintro t ⟨z, -, -, rfl⟩; exact hpos z⟩
  have hle : mu ≤ c ^ 2 * BookProof.FarisLavine.quadForm H x := by
    rw [← hqy]; exact hmu.trans (csInf_le hbdd hmem)
  have hc2 : c ^ 2 * ‖(x : F)‖ ^ 2 = 1 := by
    rw [hc, ← mul_pow, inv_mul_cancel₀ hn.ne', one_pow]
  have := mul_le_mul_of_nonneg_right hle (sq_nonneg ‖(x : F)‖)
  calc mu * ‖(x : F)‖ ^ 2 ≤ c ^ 2 * BookProof.FarisLavine.quadForm H x * ‖(x : F)‖ ^ 2 := this
    _ = BookProof.FarisLavine.quadForm H x := by rw [mul_right_comm, hc2, one_mul]

theorem solution (H : D →ₗ[ℂ] F)
    (hpos : ∀ x : D, 0 ≤ quadForm H x) {V : Submodule ℂ F} {mu : ℝ}
    (hmu : mu ≤ ritzInf H V) (x : D) (hx : (x : F) ∈ V) :
    mu * ‖(x : F)‖ ^ 2 ≤ quadForm H x := by
  exact h44_qf_ge H hpos hmu x hx

