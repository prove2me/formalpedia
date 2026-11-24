-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux6.intH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:06:38.251397+00:00
-- url     : https://prove2.me/submissions/752e8e5e-792c-4094-9100-f31b81ee57f9

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_isAddHaarMeasure_matrix_volume
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_finrank_pi_pi_complex
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_finrank_fun
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_card_UT
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_card_LW
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_rpow4

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux6
namespace Formalism.FourierDecayAlt.P.Ux6
theorem _root_.solution (p s : ℕ) (σ : Equiv.Perm (Fin p)) (a : ℝ) (h1 : ((s * (p * 2) : ℕ) : ℝ) < a)
    (h2 : ((p * (s * 2) : ℕ) : ℝ) < a) (h3 : ((p * p * 2 : ℕ) : ℝ) < a) :
    Integrable (fun η : XiH p s σ => wtH η ^ (-a)) (muXiH p s σ) := by
  have := isAddHaarMeasure_matrix_volume s p
  have := isAddHaarMeasure_matrix_volume p s
  have iA : Integrable (fun x : Fin s → Fin p → ℂ => (1 + ‖x‖) ^ (-a)) volume :=
    integrable_one_add_norm (by rw [finrank_pi_pi_complex]; exact h1)
  have iB : Integrable (fun x : Fin p → Fin s → ℂ => (1 + ‖x‖) ^ (-a)) volume :=
    integrable_one_add_norm (by rw [finrank_pi_pi_complex]; exact h2)
  have iL : Integrable (fun x : LW σ → ℂ => (1 + ‖x‖) ^ (-a)) volume := by
    refine integrable_one_add_norm (lt_of_le_of_lt ?_ h3)
    rw [finrank_fun]
    exact_mod_cast Nat.mul_le_mul_right 2 (card_LW σ)
  have iU : Integrable (fun x : Formalism.FourierDecayAlt.G.UT p → ℂ => (1 + ‖x‖) ^ (-a)) volume := by
    refine integrable_one_add_norm (lt_of_le_of_lt ?_ h3)
    rw [finrank_fun]
    exact_mod_cast Nat.mul_le_mul_right 2 (card_UT p)
  have h := (iA.mul_prod iB).mul_prod (iL.mul_prod iU)
  refine h.congr (ae_of_all _ fun η => ?_)
  simp only [wtH]
  rw [rpow4 (by positivity) (by positivity) (by positivity) (by positivity)]
end Formalism.FourierDecayAlt.P.Ux6
