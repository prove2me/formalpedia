-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxE.rep_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:54:02.61525+00:00
-- url     : https://prove2.me/submissions/ab92458a-a17c-42e6-8420-ce5f17426495

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DetRowsZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RepIntCastMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


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
namespace Formalism.FourierDecayAlt.P.JFxE
theorem _root_.solution {d : ℕ} (c : ℂ) {a : AA k r E} (ha : Rep d a) : Rep d (c • a) := by
  obtain ⟨L, hL, h⟩ := ha
  refine ⟨L.map fun p => (c * p.1, p.2), ?_, fun Φ w => ?_⟩
  · intro p hp
    simp only [List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact hL q hq
  · rw [LinearMap.smul_apply, Pi.smul_apply, h, List.smul_sum]
    simp only [List.map_map, Function.comp_def, mul_smul]
end Formalism.FourierDecayAlt.P.JFxE
