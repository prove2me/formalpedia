-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ph.curv_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:59:52.529202+00:00
-- url     : https://prove2.me/submissions/b7f84644-c051-4ae0-a7bd-5db176a1eaa8

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCHolPh

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ph
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ph
theorem _root_.solution (u0 p q s11 sii : ℂ) (hn : u0 * star u0 = 1) (ha : (star u0 * p).re = 0)
    (hb : (star u0 * q).re = 0) (h11 : (star p * p + star u0 * s11).re = 0)
    (hII : (star q * q + star u0 * sii).re = 0) :
    ((star p + Complex.I * star q) * (p - Complex.I * q) + star u0 * (s11 + sii)).re = 0 := by
  have hn' := congrArg Complex.re hn
  simp [Complex.mul_re, Complex.mul_im, Complex.star_def] at hn' ha hb h11 hII ⊢
  linear_combination h11 + hII - 2 * (-u0.re * q.im + u0.im * q.re) * ha
    - 2 * (u0.re * p.im - u0.im * p.re) * hb + 2 * (q.re * p.im - q.im * p.re) * hn'
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ph
