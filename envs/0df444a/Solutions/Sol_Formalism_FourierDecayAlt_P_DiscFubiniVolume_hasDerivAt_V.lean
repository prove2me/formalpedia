-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DiscFubiniVolume.hasDerivAt_V
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:15:45.40213+00:00
-- url     : https://prove2.me/submissions/8b947e3c-98eb-40d6-bdb6-2e1e80f642aa

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousOnG2SymmetricInterval

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory intervalIntegral Set
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DiscFubiniVolume
namespace Formalism.FourierDecayAlt.P.DiscFubiniVolume
theorem _root_.solution {u : ℝ} (hu : u ≠ 0) (t : ℝ) :
    HasDerivAt (fun t => ee u t / (Complex.I * u)) (ee u t) t := by
  have hIu : Complex.I * (u : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hu)
  have h0 : HasDerivAt (fun t : ℝ => ((u * t : ℝ) : ℂ)) ((u : ℝ) : ℂ) t := by
    have := ((hasDerivAt_id t).const_mul u).ofReal_comp
    simpa using this
  have h1 : HasDerivAt (fun t : ℝ => Complex.I * ((u * t : ℝ) : ℂ)) (Complex.I * u) t := h0.const_mul Complex.I
  have h3 := h1.cexp.div_const (Complex.I * u)
  exact h3.congr_deriv (by rw [mul_div_assoc, div_self hIu, mul_one]; rfl)
end Formalism.FourierDecayAlt.P.DiscFubiniVolume
