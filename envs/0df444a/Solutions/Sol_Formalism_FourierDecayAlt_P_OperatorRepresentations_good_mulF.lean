-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OperatorRepresentations.good_mulF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:40:04.81569+00:00
-- url     : https://prove2.me/submissions/6253901e-1a91-4276-800b-d16d0e7c253e

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Theorems.Thm_Formalism_FourierDecayAlt_P_OperatorRepresentations_smooth_coef

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.OperatorRepresentations
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
namespace Formalism.FourierDecayAlt.P.OperatorRepresentations
theorem _root_.solution {c : Mx k r → ℂ} (hc : SmoothLev k r i D c) : Qx2.Good k r i D (mulF (E := E) c) := by
  refine ⟨fun f hf => smooth_coef hc hf, ?_, ?_⟩
  · intro f f₂ h x hx
    show c x • f x = c x • f₂ x
    rw [h x hx]
  · intro f f₂ s _ _ x _
    show c x • (f x + s • f₂ x) = c x • f x + s • (c x • f₂ x)
    rw [smul_add, smul_comm]
end Formalism.FourierDecayAlt.P.OperatorRepresentations
