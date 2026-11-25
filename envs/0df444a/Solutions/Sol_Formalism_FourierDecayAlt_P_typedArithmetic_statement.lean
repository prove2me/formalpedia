-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.typedArithmetic_statement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:52:58.593586+00:00
-- url     : https://prove2.me/submissions/ac0a67b3-9a29-44b2-b7ac-34a424d0fd7d

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MemIntegralGlOfMiddleBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_card_S
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_index_Kpp
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_index_Knat
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_index_JH
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_ratios

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.S3.TypedArithmetic := by
  intro o _ _ _ r k L volK volKpp volKnat volKH volJH volNo p1 p2 p3 p4 v1 v2 v3 cG cS cGLk cUk γ
    hG hS hGLk hUk hγ
  refine S3x3.ratios L.Kpp.index L.Knat.index L.JH.index
    (Nat.card {x : Matrix (S3.Idx r k) (S3.Idx r k) (IsLocalRing.ResidueField o) // S3.IsN x})
    volK volKpp volKnat volKH volJH volNo cG cS cGLk cUk γ ?_ ?_ ?_ ?_ ?_ p1 p2 p3 p4 v1 v2 v3 hγ
  · rw [hG]; exact_mod_cast Nat.card_pos
  · rw [hG, hUk]; exact_mod_cast S3x3.index_Kpp o L
  · rw [hG, hGLk]; exact_mod_cast S3x3.index_Knat o L
  · rw [hGLk, hUk]; exact_mod_cast S3x3.index_JH o L
  · rw [hS, hGLk]; exact_mod_cast S3x3.card_S
end Formalism.FourierDecayAlt.P
