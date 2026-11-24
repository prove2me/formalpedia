-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.germExpansionOfSteps
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:00:55.284314+00:00
-- url     : https://prove2.me/submissions/ebba44b4-bcf7-4358-b7f6-f39286f47ac7

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermExpansionOfSteps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.A6.GermAssemble := by
  intro hHead hPhi K _ _ _ R ψ hD hn m hm γ hγ h Q hQ hQu
  obtain ⟨L₀, Λ₀, hL₀, hΛ₀, hΦ⟩ := hHead K R ψ hD hn m h Q hQ hQu
  obtain ⟨V, hV, hG⟩ := hPhi K R ψ hD hn m hm γ hγ L₀ Λ₀ Q hL₀ hΛ₀ hQ hQu
  refine ⟨V, hV, fun t c ht hc n' Z' => ?_⟩
  obtain ⟨Φ, hyp, h1, h2⟩ := hΦ n' Z'
  rw [h1 t c, hG Φ hyp t c ht hc]
  congr 1
  funext z
  exact (h2 z).symm
end Formalism.FourierDecayAlt.P
