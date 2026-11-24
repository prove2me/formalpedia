-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux8.cont_DjU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:42:20.84328+00:00
-- url     : https://prove2.me/submissions/be13947a-91f2-4cae-8e4b-f7541a9e9c16

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SeminormCompletion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux8
open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P.Ux8
theorem _root_.solution (k j ρ : ℕ) : Continuous (DjU k j ρ) := by
  have h : Continuous (fun g : B.Mat k (j + ρ) => Zh k j ρ g) :=
    continuous_matrix fun a b => by
      unfold Zh
      exact continuous_id.matrix_elem _ _
  exact h.matrix_det
end Formalism.FourierDecayAlt.P.Ux8
