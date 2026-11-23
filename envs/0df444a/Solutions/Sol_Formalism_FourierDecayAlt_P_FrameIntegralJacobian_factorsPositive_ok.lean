-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FrameIntegralJacobian.factorsPositive_ok
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:47.945111+00:00
-- url     : https://prove2.me/submissions/a1b0e3f8-c448-4ec7-9f5b-d01da8a1d4c4

import Definitions.Def_Formalism_HermitianCurvature_LowerBlockNormalisedBoundFromComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameIntegralJacobian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FrameIntegralJacobian
open Formalism.FourierDecayAlt.PairingProductCorollary
namespace Formalism.FourierDecayAlt.P.FrameIntegralJacobian
theorem _root_.solution : FactorsPositive := by
  unfold FactorsPositive
  refine ⟨fun D h0 h1 => ?_, fun d h1 h2 => ?_, fun D h0 h1 => div_neg_of_pos_of_neg h0 (by linarith)⟩
  · simp only [div_pos_iff, lt_abs]
    constructor
    · rintro ⟨⟨ha, hb⟩ | ⟨ha, hb⟩, ⟨hc, hd⟩ | ⟨hc, hd⟩⟩ <;>
        first | (left; linarith) | (right; linarith) | (exfalso; linarith)
    · rintro (h | h)
      · exact ⟨Or.inl ⟨by linarith, by linarith⟩, Or.inl ⟨by linarith, by linarith⟩⟩
      · exact ⟨Or.inr ⟨by linarith, by linarith⟩, Or.inr ⟨by linarith, by linarith⟩⟩
  · simp only [div_pos_iff]
    constructor
    · rintro ⟨⟨ha, hb⟩ | ⟨ha, hb⟩, ⟨hc, hd⟩ | ⟨hc, hd⟩⟩ <;>
        first | (left; linarith) | (right; linarith) | (exfalso; linarith)
    · rintro (h | h)
      · exact ⟨Or.inr ⟨by linarith, by linarith⟩, Or.inr ⟨by linarith, by linarith⟩⟩
      · exact ⟨Or.inl ⟨by linarith, by linarith⟩, Or.inl ⟨by linarith, by linarith⟩⟩
end Formalism.FourierDecayAlt.P.FrameIntegralJacobian
