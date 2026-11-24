-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RealWeightedForms.re_mul_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:22:36.975992+00:00
-- url     : https://prove2.me/submissions/ed848b69-bc80-4d6c-a435-5f6056f6ee31

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualKernelLemmas
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RealWeightedForms

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RealWeightedForms
open Finset Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities Formalism.FourierDecayAlt.P.DualKernelLemmas
open scoped Matrix
namespace Formalism.FourierDecayAlt.P.RealWeightedForms
theorem _root_.solution (u v : ℂ) (r : ℝ) (hu : u.im = 0) : (u * v / r).re = u.re * v.re / r := by
  rw [Complex.div_ofReal_re, Complex.mul_re, hu, zero_mul, sub_zero]
end Formalism.FourierDecayAlt.P.RealWeightedForms
