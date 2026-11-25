-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.expI_th_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:44:18.599667+00:00
-- url     : https://prove2.me/submissions/d0103ad3-0f13-4d7c-beaf-96541c231c11

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ImCircleIntegral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThShiftInt
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_th_shift_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Filter Topology Complex MeasureTheory intervalIntegral
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
noncomputable section
variable {TT : ℝ} {α : ℂ → ℂ}
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
theorem _root_.solution (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT))
    (hcurv : ∀ ζ : ℂ, TT < Complex.normSq ζ → (wZb α ζ).re = 0)
    (hhol : ∃ n : ℤ, (circleIntegral α 0 (TT + 1)).im = Real.pi * n)
    {w w' : ℂ} (hw : w ∈ Hh TT) (hw' : w' ∈ Hh TT) (he : Complex.exp w = Complex.exp w') :
    Complex.exp (I * (th TT α w : ℂ)) = Complex.exp (I * (th TT α w' : ℂ)) := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 he
  obtain ⟨m, hm⟩ := hhol
  have h := th_shift_int hTT hα hcurv n w' hw'
  rw [← hn, hm] at h
  apply Complex.exp_eq_exp_iff_exists_int.2
  refine ⟨n * m, ?_⟩
  rw [h]
  push_cast
  ring
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
