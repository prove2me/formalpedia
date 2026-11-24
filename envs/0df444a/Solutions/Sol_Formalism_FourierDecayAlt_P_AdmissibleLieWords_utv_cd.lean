-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdmissibleLieWords.utv_cd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:21:47.018118+00:00
-- url     : https://prove2.me/submissions/49b17b26-9a89-4005-9660-37682795708f

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleOfUnitWords
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Sq2UnitOfEqOneOfSq2EqDiv
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_Phh_cd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Set
open scoped ComplexConjugate ContDiff Manifold Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.AdmissibleLieWords
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords
theorem _root_.solution {k r m : ℕ} {ε T : ℝ} (hε : 0 < ε) {Gp : Mat k r → ℝ} {om : Mat k r → Fin m → ℂ}
    (hG : ContDiff ℝ ∞ (fun g => ((Gp g : ℝ) : ℂ))) (ho : ∀ a, ContDiff ℝ ∞ (fun g => om g a)) :
    ContDiff ℝ ∞ (utv ε T Gp om) := by
  refine contDiff_pi.2 fun a => ?_
  simp only [utv]
  exact contDiff_const.mul (((Phh_cd hε).comp hG).mul (ho a))
end Formalism.FourierDecayAlt.P.AdmissibleLieWords
