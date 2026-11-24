-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBG.polyRepN_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:23:34.271852+00:00
-- url     : https://prove2.me/submissions/88b0bf6a-406f-4238-812c-f943cd1856f1

import Definitions.Def_Formalism_HermitianCurvature_StatementD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeadingTermIdentity
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGLet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBG
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {E : Type*} [AddCommGroup E] [Module ℂ E]
namespace Formalism.FourierDecayAlt.P.PBG
theorem _root_.solution {d : ℕ} {f : ℂ → E} {top : E} (h : PolyRepN d f top) (s : ℂ) :
    PolyRepN d (fun u => s • f u) (s • top) := by
  obtain ⟨c, hc, hf⟩ := h
  refine ⟨fun l => s • c l, by beta_reduce; rw [hc], fun u => ?_⟩
  beta_reduce
  rw [hf u, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [smul_comm]
end Formalism.FourierDecayAlt.P.PBG
