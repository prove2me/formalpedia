-- Prove2me | solution 1 for BookProof.WallEsaSemibounded.opCc_quadratic_form
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-17T20:07:38.415873+00:00
-- url     : https://prove2.me/submissions/72fd1772-0a9e-4c41-b7e3-265f91983dfd

-- Generated from ChapterWallEsaSemibounded.lean — solution of BookProof.WallEsaSemibounded.opCc_quadratic_form
import Mathlib
import Definitions.Def_ChapterWallEsaSemibounded
import Theorems.Thm_BookProof_StrichartzWave_inner_toLp_left
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterScalaronWallEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStrichartzWave
import Theorems.Thm_BookProof_ScalaronEsa_opCc_apply
import Theorems.Thm_BookProof_ScalaronEsa_ccEquiv_coe
import Theorems.Thm_BookProof_ScalaronEsa_mulCc_apply
open BookProof.WallEsaSemibounded











open MeasureTheory SchwartzMap
open BookProof.FarisLavine BookProof.StrichartzWave BookProof.ScalaronEsa
open BookProof.ScalaronWallEsa

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

set_option maxHeartbeats 1000000 in
theorem solution (V : ℝ → ℝ) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (f : ccSchwartz ℝ) :
    (inner ℂ (opCc V hV (ccEquiv ℝ f))
        ((ccEquiv ℝ f : ccDomain ℝ) : Lp ℂ 2 (volume : Measure ℝ)) : ℂ)
      = ((∫ x, V x * ‖(f : 𝓢(ℝ, ℂ)) x‖ ^ 2 : ℝ) : ℂ) := by

  rw [opCc_apply, ccEquiv_coe, inner_toLp_left, ← integral_complex_ofReal]
  refine integral_congr_ae ?_
  filter_upwards [(f : 𝓢(ℝ, ℂ)).coeFn_toLp 2 (volume : Measure ℝ)] with x hx
  rw [hx]
  simp only [mulCc_apply, map_mul, Complex.conj_ofReal, Complex.ofReal_mul]
  rw [mul_assoc, Complex.normSq_eq_conj_mul_self.symm, Complex.sq_norm]
