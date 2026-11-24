-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ShearMeasurability.shear_meas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:14:15.415637+00:00
-- url     : https://prove2.me/submissions/bbb14e8e-696c-42c6-b8e8-fa8aba85f453

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LowerParabolicCoordinates
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ShearMeasurability
import Theorems.Thm_Formalism_FourierDecayAlt_P_ShearMeasurability_shearMap_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.ShearMeasurability
variable {m : ℕ} (w : Equiv.Perm (Fin m))
namespace Formalism.FourierDecayAlt.P.ShearMeasurability
theorem _root_.solution : Measurable (fun x => mulMap w (eSplit w x)) := by
  have e : (fun x => mulMap w (eSplit w x)) =
      fun x q => x q + ∑ k, aX w x q.1.1 k * bX w x k q.1.2 := by
    funext x q
    exact shearMap_apply w x q
  rw [e]
  have ha : ∀ i k, Measurable fun x : C2.Lidx m → ℂ => aX w x i k := by
    intro i k
    by_cases h : k < i ∧ w.symm k < w.symm i
    · simp only [aX, dif_pos h]
      exact measurable_pi_apply _
    · simp only [aX, dif_neg h]
      exact measurable_const
  have hb : ∀ k j, Measurable fun x : C2.Lidx m → ℂ => bX w x k j := by
    intro k j
    by_cases h : j < k ∧ w.symm k < w.symm j
    · simp only [bX, dif_pos h]
      exact measurable_pi_apply _
    · simp only [bX, dif_neg h]
      exact measurable_const
  apply measurable_pi_lambda
  intro q
  exact (measurable_pi_apply q).add (Finset.measurable_sum _ fun k _ => (ha _ _).mul (hb _ _))
end Formalism.FourierDecayAlt.P.ShearMeasurability
