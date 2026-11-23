-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx1.dsMeas
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:25:10.794524+00:00
-- url     : https://prove2.me/submissions/b512faee-175c-4535-adeb-8a86a4823f0f

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaEprimeFromSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StepClaimFromStepsFull
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_meas_iterDeriv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx1
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
noncomputable section
namespace Formalism.FourierDecayAlt.P.LEx1
theorem _root_.solution : DsMeas := by
  intro B S hMeas hI4 Y hY p k
  obtain ⟨c, hc⟩ := hI4 Y hY
  have := meas_iterDeriv (fun s ω => S.gs Y s ω k) (fun ω => by
      have : (fun s : ℝ => S.gs Y s ω k) = fun s : ℝ => ∑ q ∈ range (S.r + 1 + 1), (s : ℂ) ^ q * c q ω k := by
        funext s; exact hc s ω k
      rw [this]
      apply ContDiff.sum
      intro q _
      exact (Complex.ofRealCLM.contDiff.pow q).mul contDiff_const)
    (fun s => (hMeas.2.2 Y hY).2 s k) p 0
  exact this
end Formalism.FourierDecayAlt.P.LEx1
