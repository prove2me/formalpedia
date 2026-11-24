-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxE.EH_HS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:21:19.156451+00:00
-- url     : https://prove2.me/submissions/bb617798-2bcc-469d-9f02-b5b52a8189c6

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Hpart2EqZeroOfInLie
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EHcChange
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_EH_psi
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_rep1

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
theorem _root_.solution : HS (Q.EH (E := E) k r) := by
  intro a b c f hf g hg
  obtain ⟨U, F, hU, hgU, hF, hff⟩ := rep1 hf hg
  rw [EH_psi (φ := fun x => c • f x) hU hgU hg (hF.const_smul c)
      (fun h hh hG => by simp only [hff h hh hG, Pi.smul_apply]) a b,
    EH_psi hU hgU hg hF hff a b]
  simp only [Psi]
  show c • fderiv ℝ F g (g * hpart1 (Hpk k r) (Matrix.single a b 1)) +
      Complex.I • c • fderiv ℝ F g (g * hpart2 (Hpk k r) (Matrix.single a b 1)) = _
  rw [smul_add, smul_comm Complex.I c]
end Formalism.FourierDecayAlt.P.JFxE
