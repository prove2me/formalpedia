-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.realCharConj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:13:23.048579+00:00
-- url     : https://prove2.me/submissions/3dd7b5d0-e6c0-4b87-a561-3a7b2e6d9d4e

import Definitions.Def_Formalism_LandauZeroFreeBounds_NoZeroComplexOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_TrivReal
import Theorems.Thm_Formalism_ZeroFreeDirichlet_conj_LFunction_conj_of_sq_eq_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution : RealConj := by
  intro q _ χ hχ h1 s
  have hL : Differentiable ℂ (DirichletCharacter.LFunction χ) :=
    DirichletCharacter.differentiable_LFunction h1
  have hG : Differentiable ℂ
      (fun z => starRingEnd ℂ (DirichletCharacter.LFunction χ (starRingEnd ℂ z))) := by
    intro z
    have := (hL (starRingEnd ℂ z)).conj_conj
    rw [Complex.conj_conj] at this
    exact this
  have heq : (fun z => starRingEnd ℂ (DirichletCharacter.LFunction χ (starRingEnd ℂ z))) =
      DirichletCharacter.LFunction χ := by
    refine AnalyticOnNhd.eq_of_eventuallyEq (z₀ := 2) (analyticOnNhd_univ_iff_differentiable.2 hG)
      (analyticOnNhd_univ_iff_differentiable.2 hL) ?_
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
    exact conj_LFunction_conj_of_sq_eq_one χ hχ z hz
  have := congrFun heq (starRingEnd ℂ s)
  simp only [Complex.conj_conj] at this
  exact this.symm
end Formalism.ZeroFreeDirichlet
