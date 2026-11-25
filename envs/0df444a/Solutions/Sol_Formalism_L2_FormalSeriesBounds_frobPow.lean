-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.frobPow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:16:19.629057+00:00
-- url     : https://prove2.me/submissions/1765c375-e4f4-4dee-9f1c-53a05ba9d259

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_FrobSerSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffPowCharFrobenius
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FrobP_coeff_pow_char_frobenius

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open ValuationNonnegativity
open FrobP
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution : FrobPowSt := by
  intro C _ V f hf
  refine ⟨fun n => ?_, fun m hm => ?_⟩
  · have h := FrobP.coeff_pow_char_frobenius (V := V) (V.l * n) f hf
    rwa [if_pos (dvd_mul_right _ _), Nat.mul_div_cancel_left _ V.l_prime.pos] at h
  · have h := FrobP.coeff_pow_char_frobenius (V := V) m f hf
    rwa [if_neg hm, sub_zero] at h
end Formalism.L2.FormalSeriesBounds
