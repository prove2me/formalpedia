-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxE.ev_Tm_Lf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:04:41.538903+00:00
-- url     : https://prove2.me/submissions/4f2a8fae-6b33-4357-8004-71efb801711c

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RepIntCastMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BridgeQminor

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
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E))
namespace Formalism.FourierDecayAlt.P.JFxE
theorem _root_.solution (v : ℂ) (a b : Fin (2 * r + k + 1)) (φ : Mat k r → E) (x : Mat k r) :
    ev Eop (Tm (Lf k r E) v a b) φ x = Top Eop v a b φ x := by
  simp only [ev, Formalism.REAL.Tm, Formalism.QuantumDeterminants.Top]
  split_ifs <;> simp [Lf, Formalism.FourierDecayAlt.P.JFxE.ell, Phi, Fw]
end Formalism.FourierDecayAlt.P.JFxE
