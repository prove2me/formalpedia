-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr3.eeConj_abs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:05:10.605116+00:00
-- url     : https://prove2.me/submissions/a39359ad-d788-4110-9fb4-6801e2895e29

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleGD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleSS
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_L0ConstantPartCommute

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr3
namespace Formalism.FourierDecayAlt.P.Fr3
theorem _root_.solution {B : Type} [Ring B] (G Gi x xi l0 z κ κi e D : B)
    (hG : Gi * G = 1) (hκ : κi * κ = 1) (hx : xi * x = 1)
    (c1 : l0 * G = G * (l0 - z)) (cxl : Commute x l0) (cxz : Commute x z) (cxκ : Commute x κ)
    (cκG : Commute κ G) (ceG : Commute e G)
    (h : G * x * (l0 + κ * e) - (l0 + κ * e) * (G * x) = -(G * x * (-z + κ * D))) :
    xi * e * x - D = e := by
  have e1 : (l0 + κ * e) * (G * x) = G * (x * l0) - G * (x * z) + G * (κ * (e * x)) := by
    calc (l0 + κ * e) * (G * x) = (l0 * G) * x + κ * (e * G) * x := by noncomm_ring
      _ = G * (l0 - z) * x + κ * (G * e) * x := by rw [c1, ceG.eq]
      _ = G * (l0 * x) - G * (z * x) + (κ * G) * (e * x) := by noncomm_ring
      _ = _ := by rw [← cxl.eq, ← cxz.eq, cκG.eq, mul_assoc]
  have e2 : G * x * (l0 + κ * e) = G * (x * l0) + G * (κ * (x * e)) := by
    calc G * x * (l0 + κ * e) = G * (x * l0) + G * ((x * κ) * e) := by noncomm_ring
      _ = _ := by rw [cxκ.eq, mul_assoc]
  have e3 : G * x * (-z + κ * D) = -(G * (x * z)) + G * (κ * (x * D)) := by
    calc G * x * (-z + κ * D) = -(G * (x * z)) + G * ((x * κ) * D) := by noncomm_ring
      _ = _ := by rw [cxκ.eq, mul_assoc]
  rw [e1, e2, e3] at h
  have h' : G * (κ * (x * e + x * D - e * x)) = 0 := by
    have t : G * (κ * (x * e + x * D - e * x)) =
        (G * (x * l0) + G * (κ * (x * e)) - (G * (x * l0) - G * (x * z) + G * (κ * (e * x)))) -
          -(-(G * (x * z)) + G * (κ * (x * D))) := by noncomm_ring
    rw [t, h, sub_self]
  have h'' : x * e + x * D - e * x = 0 := by
    calc x * e + x * D - e * x = κi * (Gi * (G * (κ * (x * e + x * D - e * x)))) := by
          rw [← mul_assoc Gi, hG, one_mul, ← mul_assoc κi, hκ, one_mul]
      _ = 0 := by rw [h', mul_zero, mul_zero]
  have h3 : e * x = x * e + x * D := (sub_eq_zero.mp h'').symm
  rw [mul_assoc, h3, mul_add, ← mul_assoc, ← mul_assoc, hx, one_mul, one_mul, add_sub_cancel_right]
end Formalism.FourierDecayAlt.P.Fr3
