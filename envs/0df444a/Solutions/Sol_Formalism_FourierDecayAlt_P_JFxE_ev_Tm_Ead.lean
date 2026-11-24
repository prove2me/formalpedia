-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxE.ev_Tm_Ead
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:04:40.493799+00:00
-- url     : https://prove2.me/submissions/2f135df2-b535-4652-8293-b7fb12c34da5

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
theorem _root_.solution (P Q : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (v : ℂ) (c d : Fin (2 * r + k + 1))
    (φ : Mat k r → E) (x : Mat k r) :
    ev Eop (Tm (Ead (Lf k r E) P Q) v c d) φ x =
      (if c = d then v • φ x else 0) + ∑ a, ∑ b, (P a c * Q d b) • Eop a b φ x := by
  simp only [ev, Formalism.REAL.Tm, Ead]
  split_ifs <;> simp [Lf, Formalism.FourierDecayAlt.P.JFxE.ell, Phi, Fw, LinearMap.sum_apply, Finset.sum_apply]
end Formalism.FourierDecayAlt.P.JFxE
