-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.jdh_ckOn_of_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:00:09.381929+00:00
-- url     : https://prove2.me/submissions/6142525a-9c0d-4e4e-bc4a-22fd242e7042

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDHatOpA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ZinvBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDHatPolyOK

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP
noncomputable section
open scoped ContDiff
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH Formalism.FourierDecayAlt.P.AdmissibleLieWords
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P.CutMP
theorem _root_.solution {k r : ℕ} {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E'] {f : B.Mat k r → E'}
    (hf : ContDiff ℝ ∞ f) (UU : Set (B.Mat k r)) : B.CkOn ⊤ UU f :=
  fun _ _ => ⟨Set.univ, f, isOpen_univ, trivial, hf.contDiffOn, fun _ _ _ => rfl⟩
end Formalism.FourierDecayAlt.P.CutMP
