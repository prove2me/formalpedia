-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrderIndexAndStrata.sFrame
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:37:01.194849+00:00
-- url     : https://prove2.me/submissions/2877e52c-8f31-4796-a030-0582f352658f

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointwiseStabiliserParametrisationBijective
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrderIndexAndStrata
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrderIndexAndStrata_det_mid
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrderIndexAndStrata_mid_form

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrderIndexAndStrata
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni)
open Formalism.FourierDecayAlt.S3
namespace Formalism.FourierDecayAlt.P.OrderIndexAndStrata
theorem _root_.solution (hS : SExplicit) : SIsFrameStabiliser := by
  intro A _ r k x hx
  rw [hS]
  constructor
  · rintro ⟨h11, h33, h21, h31, h32, h, hh, h22⟩
    refine ⟨⟨h11, h21, h31, fun a => ?_, fun a => ?_⟩, ⟨h33, h32, fun b => ?_, fun b => ?_⟩⟩
    · rw [h22]; rcases a with a | ⟨⟩ <;> simp [midEmb]
    · simp [h32]
    · rw [h22]; rcases b with b | ⟨⟩ <;> simp [midEmb]
    · simp [h21]
  · rintro ⟨⟨h11, h21, h31, hc, -⟩, ⟨h33, h32, hr, -⟩⟩
    obtain ⟨h, hh, he⟩ := mid_form (b22 x) (det_mid x hx h21 h31 h32) hc hr
    exact ⟨h11, h33, h21, h31, h32, h, hh, he⟩
end Formalism.FourierDecayAlt.P.OrderIndexAndStrata
