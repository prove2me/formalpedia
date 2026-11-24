-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxE.Psi_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:57:16.250624+00:00
-- url     : https://prove2.me/submissions/4d302bf7-b0df-4ded-ba44-d3f07dab17c0

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BridgeQminor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Hpart2EqZeroOfInLie
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_hp1_real
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_hpart2_ofReal_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_D_real

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxE
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity Formalism.FourierDecayAlt.P.JFxB
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.JFxE
theorem _root_.solution (D : Mat k r →L[ℝ] E) (g Z : Mat k r) (x : ℝ) : Psi D g ((x : ℂ) • Z) = (x : ℂ) • Psi D g Z := by
  simp only [Psi, hp1_real, hpart2_ofReal_smul, D_real, smul_add]
  rw [smul_comm (x : ℂ) Complex.I]
end Formalism.FourierDecayAlt.P.JFxE
