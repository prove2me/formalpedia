-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.ex_rect_double
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:59:38.578471+00:00
-- url     : https://prove2.me/submissions/780f2797-d5f6-4d92-bb68-470aca3a4c7d

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplLF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplRect
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplRectF
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_ex_phi_hasDerivAt
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_ex_phi_differentiableOn
import Theorems.Thm_Formalism_ZF_rectangle_double_pole


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.ZeroFreeDirichlet
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution (y : ℝ) (hy : 0 < y) (x₀ x₁ y₀ y₁ : ℝ) (hx₀ : 0 < x₀) (hx₀1 : x₀ < 1) (hx₁ : 1 < x₁)
    (hy₀ : y₀ < 0) (hy₁ : 0 < y₁) :
    Formalism.ZF.rectInt (fun w => exKer y w / (w - 1)) x₀ x₁ y₀ y₁ =
      2 * Real.pi * I * ((y : ℂ) * (Real.log y : ℂ) - y) := by
  have hb : HasDerivAt (fun w : ℂ => (y : ℂ) ^ w / w) ((y : ℂ) * (Real.log y : ℂ) - y) 1 := ex_phi_hasDerivAt y hy
  have hU : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have h1U : {w : ℂ | 0 < w.re} ∈ nhds (1 : ℂ) := hU.mem_nhds (by simp)
  have hφd : DifferentiableOn ℂ (fun w : ℂ => (y : ℂ) ^ w / w) {w : ℂ | 0 < w.re} := ex_phi_differentiableOn y hy
  have hG : DifferentiableOn ℂ (dslope (dslope (fun w : ℂ => (y : ℂ) ^ w / w) 1) 1) {w : ℂ | 0 < w.re} :=
    (differentiableOn_dslope h1U).2 ((differentiableOn_dslope h1U).2 hφd)
  have hd1 : dslope (fun w : ℂ => (y : ℂ) ^ w / w) 1 1 = (y : ℂ) * (Real.log y : ℂ) - y := by
    rw [dslope_same, hb.deriv]
  refine Formalism.ZF.rectangle_double_pole (fun w => exKer y w / (w - 1))
    (dslope (dslope (fun w : ℂ => (y : ℂ) ^ w / w) 1) 1) (y : ℂ) ((y : ℂ) * (Real.log y : ℂ) - y) 1 x₀ x₁ y₀ y₁
    (by simpa using hx₀1) (by simpa using hx₁) (by simpa using hy₀) (by simpa using hy₁)
    ⟨{w : ℂ | 0 < w.re}, hU, ?_, hG⟩ ?_
  · intro z hz
    rw [Complex.mem_reProdIm, Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)] at hz
    show 0 < z.re
    linarith [hz.1.1]
  · intro w hw
    have hw1 : w - 1 ≠ 0 := sub_ne_zero.mpr hw
    rw [dslope_of_ne _ hw, slope_def_field, dslope_of_ne _ hw, slope_def_field, hd1]
    simp only [exKer, Complex.cpow_one, div_one]
    by_cases h0 : w = 0
    · subst h0
      simp
      ring
    · field_simp
      ring
end Formalism.HermitianLattices.Ext.PrimesInProgressions
