-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.sym_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:18:56.565793+00:00
-- url     : https://prove2.me/submissions/8e48b988-a2f8-4657-b101-be2e7f614d84

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FderivDecomp
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BasePointMemHalfPlane

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Filter Topology Complex
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
noncomputable section
variable {TT : ℝ} {α : ℂ → ℂ}
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
theorem _root_.solution (A b ζ h k : ℂ) (hb : b.re = 0) :
    ((A * h + b * ζ * (starRingEnd ℂ) ζ * (starRingEnd ℂ) h) * k).im =
      ((A * k + b * ζ * (starRingEnd ℂ) ζ * (starRingEnd ℂ) k) * h).im := by
  simp only [Complex.mul_im, Complex.mul_re, Complex.add_im, Complex.add_re, Complex.conj_re,
    Complex.conj_im, hb]
  ring
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
