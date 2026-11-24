-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.wir_hasLineDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:54:05.132562+00:00
-- url     : https://prove2.me/submissions/4645eb94-1d03-4d22-bf6f-05b9282b8d5e

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WirtingerIntegrationByParts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
open Formalism.FourierDecayAlt.G MeasureTheory
namespace Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
theorem _root_.solution {d : ℕ} (β t : ℂ) {g : (Fin d → ℂ) → ℂ} {x : Fin d → ℂ}
    (hg : DifferentiableAt ℂ g x) (v : Fin d → ℂ) :
    HasLineDerivAt ℝ (fun y => psi β (g y / t))
      (psi β (g x / t) * (Complex.I * (((β / t * fderiv ℂ g x v).re : ℝ) : ℂ))) x v := by
  have h0 : HasFDerivAt g ((fderiv ℂ g x).restrictScalars ℝ) x := hg.hasFDerivAt.restrictScalars ℝ
  have h1 := h0.const_mul (β / t)
  have h2 := Complex.reCLM.hasFDerivAt.comp x h1
  have h3 := Complex.ofRealCLM.hasFDerivAt.comp x h2
  have h4 := (h3.const_mul Complex.I).cexp
  have h5 := h4.hasLineDerivAt v
  have e : (fun y => psi β (g y / t)) =
      fun y => Complex.exp (Complex.I * (Complex.ofRealCLM ∘ Complex.reCLM ∘ fun y => β / t * g y) y) := by
    funext y
    simp only [psi, Function.comp, Complex.ofRealCLM_apply, Complex.reCLM_apply]
    congr 4
    ring
  have ev : psi β (g x / t) * (Complex.I * (((β / t * fderiv ℂ g x v).re : ℝ) : ℂ)) =
      (Complex.exp (Complex.I * (Complex.ofRealCLM ∘ Complex.reCLM ∘ fun y => β / t * g y) x) •
        Complex.I • Complex.ofRealCLM ∘SL Complex.reCLM ∘SL
          ((β / t) • ContinuousLinearMap.restrictScalars ℝ (fderiv ℂ g x))) v := by
    have := congrFun e x
    rw [this]
    simp
  rw [e, ev]
  exact h5
end Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
