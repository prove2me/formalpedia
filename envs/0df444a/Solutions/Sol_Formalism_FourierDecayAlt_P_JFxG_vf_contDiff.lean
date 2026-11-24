-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxG.vf_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:55:45.500702+00:00
-- url     : https://prove2.me/submissions/be081979-1c93-483e-9528-b56e9df73d99

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaConjOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactSupportFiniteClass
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxG_vf_eq_b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxG
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.JFxG
theorem _root_.solution {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] (b : Bool) {X g : P → Mat k r}
    (hX : ContDiff ℝ ∞ X) (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (fun q => vf b (X q) (g q)) := by
  cases b
  · have h := ((mulRb k r).contDiff.comp hX).clm_apply hg
    first
    | exact h.congr fun q => by rw [vf_eq_b]; rfl
    | (convert h using 1; funext q; rw [vf_eq_b]; rfl)
  · have h := (((mulLb k r).contDiff.comp hX).clm_apply hg).neg
    first
    | exact h.congr fun q => by rw [vf_eq_b]; rfl
    | (convert h using 1; funext q; rw [vf_eq_b]; rfl)
end Formalism.FourierDecayAlt.P.JFxG
