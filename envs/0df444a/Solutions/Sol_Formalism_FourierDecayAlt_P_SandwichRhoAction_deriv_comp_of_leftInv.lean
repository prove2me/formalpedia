-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SandwichRhoAction.deriv_comp_of_leftInv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:24:24.93002+00:00
-- url     : https://prove2.me/submissions/f6c1279f-c16c-4c65-a12d-0cd2adc5e7d5

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SandwichRhoAction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SandwichRhoAction
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P.SandwichRhoAction
theorem _root_.solution {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (L : E →L[ℝ] F) (M : F →L[ℝ] E) (hML : ∀ x, M (L x) = x) (φ : ℝ → E) (t : ℝ) :
    deriv (fun s => L (φ s)) t = L (deriv φ t) := by
  by_cases h : DifferentiableAt ℝ φ t
  · exact (L.hasFDerivAt.comp_hasDerivAt t h.hasDerivAt).deriv
  · have h' : ¬ DifferentiableAt ℝ (fun s => L (φ s)) t := by
      intro hd
      apply h
      have hφ : (fun s => M (L (φ s))) = φ := funext fun s => hML (φ s)
      rw [← hφ]
      exact M.differentiableAt.comp t hd
    rw [deriv_zero_of_not_differentiableAt h, deriv_zero_of_not_differentiableAt h', map_zero]
end Formalism.FourierDecayAlt.P.SandwichRhoAction
