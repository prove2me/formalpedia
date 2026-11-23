-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.vfact_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:51:52.707256+00:00
-- url     : https://prove2.me/submissions/48ed3c09-bca7-43ff-85c7-5a2026b72c58

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IVP_mul
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_vchoose_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.gammaIntegralityLemmas
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace Formalism.GM.gammaIntegralityLemmas
theorem _root_.solution {a b T B : ℕ} (h : a + b ≤ T) (hB : Nat.log p T ≤ B) :
    padicValNat p (a + b).factorial ≤ padicValNat p a.factorial + padicValNat p b.factorial + B := by
  have e := Nat.add_choose_mul_factorial_mul_factorial a b
  have h1 : padicValNat p (a + b).factorial =
      padicValNat p ((a + b).choose b) + padicValNat p a.factorial + padicValNat p b.factorial := by
    rw [← e, padicValNat.mul (Nat.mul_ne_zero (Nat.choose_pos (by omega)).ne' (Nat.factorial_pos _).ne') (Nat.factorial_pos _).ne',
      padicValNat.mul (Nat.choose_pos (by omega)).ne' (Nat.factorial_pos _).ne']
  have := vchoose_le (p := p) (k := b) h hB
  omega
end Formalism.GM.gammaIntegralityLemmas
