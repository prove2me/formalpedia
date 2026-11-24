-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BesselScaling.anyFromNorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:29:29.066036+00:00
-- url     : https://prove2.me/submissions/0a867166-7b42-4ed3-97d5-e19a04a3c976

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaBOfComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselScaling
import Theorems.Thm_Formalism_FourierDecayAlt_P_BesselScaling_betaInf_scale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BesselScaling
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P.BesselScaling
theorem _root_.solution : LemmaBNorm → IntNormB → LemmaBAny := by
  intro hN hB k r Wp Wq _ _ _ _ _ _ D A hA
  obtain ⟨c, ⟨hc, hF⟩, -⟩ := hB k r Wp Wq D
  have hF' : IntFormula (scaleG D c hc) := hF
  obtain ⟨h1, h2, h3, h4⟩ := hN k r Wp Wq (scaleG D c hc) A hA hF'
  refine ⟨c, hc, hF, h1, ?_, ?_, h4⟩
  · intro F F' hF1 hF2
    have hb : beta (scaleG D c hc) F F' = beta D F F' := rfl
    rw [← hb, h2 F F' hF1 hF2, betaInf_scale]
  · intro UU Θ hU hS hC F F' hF1 hF2 hs1 hs2 hI1 hI2 hI3 hI4 hIC
    exact h3 UU Θ hU hS hC F F' hF1 hF2 hs1 hs2 hI1 hI2 hI3 hI4
      (fun p hp T hT i j hij hj => (hIC p hp T hT i j hij hj).smul_measure_nnreal)
end Formalism.FourierDecayAlt.P.BesselScaling
