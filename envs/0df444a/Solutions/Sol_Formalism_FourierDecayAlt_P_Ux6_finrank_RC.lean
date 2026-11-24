-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux6.finrank_RC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:33:06.17881+00:00
-- url     : https://prove2.me/submissions/4ce60cd5-fbef-4ff9-83a2-dfa7e5e52b5f

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_finrank_pi_pi_complex
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_finrank_fun
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_card_UT

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
theorem _root_.solution (k j ρ : ℕ) : Module.finrank ℝ (RC k j ρ) ≤ (2 * ρ + k + 1) * (j * 2) + j * j * 2 + j := by
  rw [Module.finrank_prod, Module.finrank_prod, finrank_pi_pi_complex, finrank_fun]
  have h1 := card_UT j
  have h2 : Module.finrank ℝ (Fin j → ℝ) = j := by simp
  rw [h2]
  nlinarith
end Formalism.FourierDecayAlt.P.Ux6
