-- Prove2me | solution 4 for BookProof.WallEsaSemibounded.kinCcR_quadratic_form
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-20T10:58:26.371399+00:00
-- url     : https://prove2.me/submissions/bceb3aaf-c2e0-4743-b3d2-b268e8d030d3

-- Generated from ChapterWallEsaSemibounded.lean — solution of BookProof.WallEsaSemibounded.kinCcR_quadratic_form
import Mathlib
import Definitions.Def_ChapterWallEsaSemibounded
import Theorems.Thm_BookProof_WallEsaSemibounded_integral_conj_neg_deriv2_mul
import Theorems.Thm_BookProof_ScalaronWallEsa_kinOpR_apply
import Theorems.Thm_BookProof_StrichartzWave_inner_toLp_left
import Theorems.Thm_BookProof_StrichartzWave_opL2_apply
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterScalaronWallEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStrichartzWave
import Theorems.Thm_BookProof_ScalaronEsa_ccEquiv_coe
open BookProof.WallEsaSemibounded











open MeasureTheory SchwartzMap
open BookProof.FarisLavine BookProof.StrichartzWave BookProof.ScalaronEsa
open BookProof.ScalaronWallEsa

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

set_option maxHeartbeats 1000000 in
theorem solution (f : ccSchwartz ℝ) :
    (inner ℂ (kinCcR (ccEquiv ℝ f))
        ((ccEquiv ℝ f : ccDomain ℝ) : Lp ℂ 2 (volume : Measure ℝ)) : ℂ)
      = ((∫ x, ‖deriv ((f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x‖ ^ 2 : ℝ) : ℂ) := by

  have hincl : Submodule.inclusion (ccDomain_le_schwartzDomain (E := ℝ)) (ccEquiv ℝ f)
      = schwartzEquiv ℝ (f : 𝓢(ℝ, ℂ)) := Subtype.ext rfl
  have hkin : kinCcR (ccEquiv ℝ f)
      = (kinOpR (f : 𝓢(ℝ, ℂ))).toLp 2 (volume : Measure ℝ) := by
    simp only [kinCcR, LinearMap.coe_comp, Function.comp_apply, hincl, opL2_apply]
  rw [hkin, ccEquiv_coe, inner_toLp_left]
  rw [show (∫ x, (starRingEnd ℂ) ((kinOpR (f : 𝓢(ℝ, ℂ))) x)
        * ((f : 𝓢(ℝ, ℂ)).toLp 2 (volume : Measure ℝ) : ℝ → ℂ) x)
      = ∫ x, (starRingEnd ℂ) (-deriv (deriv ((f : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) x)
          * ((f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x from ?_]
  · exact integral_conj_neg_deriv2_mul _ ((f : 𝓢(ℝ, ℂ)).smooth 2) f.2
  refine integral_congr_ae ?_
  filter_upwards [(f : 𝓢(ℝ, ℂ)).coeFn_toLp 2 (volume : Measure ℝ)] with x hx
  rw [hx, kinOpR_apply]
