-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OperatorRepresentations.Rep.ite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:49:42.415876+00:00
-- url     : https://prove2.me/submissions/ca966aa9-a867-43fa-ac41-24cdb5b972c2

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Theorems.Thm_Formalism_FourierDecayAlt_P_OperatorRepresentations_rep_zero

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
namespace Rep
theorem _root_.solution {X : Module.End ℂ (SV k r i D E)} {T : (Mx k r → E) → Mx k r → E} (hX : Rep X T) (p : Prop)
    [Decidable p] : Rep (if p then X else 0) (fun f x => if p then T f x else 0) := by
  by_cases hp : p
  · simpa only [if_pos hp] using hX
  · simpa only [if_neg hp] using rep_zero
end Rep
end Formalism.FourierDecayAlt.P.OperatorRepresentations
