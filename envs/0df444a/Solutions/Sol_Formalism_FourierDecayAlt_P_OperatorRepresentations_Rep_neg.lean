-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OperatorRepresentations.Rep.neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:56:13.502061+00:00
-- url     : https://prove2.me/submissions/d9baf4fb-3233-484b-a28e-101966ea527f

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Theorems.Thm_Formalism_FourierDecayAlt_P_OperatorRepresentations_good_neg

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
theorem _root_.solution {X : Module.End ℂ (SV k r i D E)} {T : (Mx k r → E) → Mx k r → E} (hX : Rep X T) :
    Rep (-X) (fun f x => -T f x) :=
  ⟨good_neg hX.1, fun φ g hg => by
    show -(X φ).1 g = -T φ.1 g
    rw [hX.2 _ g hg]⟩
end Rep
end Formalism.FourierDecayAlt.P.OperatorRepresentations
