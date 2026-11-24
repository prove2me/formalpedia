-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxE.hp1_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:38:50.211369+00:00
-- url     : https://prove2.me/submissions/00d9d3fd-0cba-45df-997f-420a7e9729f2

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BridgeQminor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Hpart2EqZeroOfInLie

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
theorem _root_.solution (x : ℝ) (Z : Mat k r) : hpart1 (Hpk k r) ((x : ℂ) • Z) = (x : ℂ) • hpart1 (Hpk k r) Z := by
  have hs : star (x : ℂ) = (x : ℂ) := Complex.conj_ofReal x
  simp only [hpart1, Matrix.conjTranspose_smul, hs, Matrix.mul_smul, Matrix.smul_mul]
  rw [← smul_sub, smul_comm]
end Formalism.FourierDecayAlt.P.JFxE
