-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxE.Psi_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:22:36.492855+00:00
-- url     : https://prove2.me/submissions/37998d3b-a87f-4cdb-bb25-998e5249f2e9

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BridgeQminor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Hpart2EqZeroOfInLie
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_Psi_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_Psi_real
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_Psi_I

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
theorem _root_.solution (D : Mat k r →L[ℝ] E) (g Z : Mat k r) (c : ℂ) : Psi D g (c • Z) = c • Psi D g Z := by
  have hc := Complex.re_add_im c
  calc Psi D g (c • Z) = Psi D g ((c.re : ℂ) • Z + (c.im : ℂ) • (Complex.I • Z)) := by
        rw [smul_smul, ← add_smul, hc]
    _ = (c.re : ℂ) • Psi D g Z + (c.im : ℂ) • (Complex.I • Psi D g Z) := by
        rw [Psi_add, Psi_real, Psi_real, Psi_I]
    _ = c • Psi D g Z := by
        rw [smul_smul, ← add_smul, hc]
end Formalism.FourierDecayAlt.P.JFxE
