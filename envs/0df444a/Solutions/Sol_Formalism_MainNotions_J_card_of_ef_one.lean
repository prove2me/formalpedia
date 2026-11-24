-- Prove2me | solution 1 for Formalism.MainNotions.J.card_of_ef_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:42:49.373052+00:00
-- url     : https://prove2.me/submissions/5882b4ee-59cc-4f3b-9541-c11a3ea45f0a

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_AdmissibleParameterJoins_SfromGLt
import Theorems.Thm_Formalism_MainNotions_J_sum_ef

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.J
open Ideal NumberField IsDedekindDomain
variable (K : Type) [Field K] [NumberField K] (p : ℕ)
namespace Formalism.MainNotions.J
theorem _root_.solution (hp : p.Prime)
    (h : ∀ P ∈ IsDedekindDomain.primesOverFinset (span {(p : ℤ)}) (𝓞 K),
      (span {(p : ℤ)}).ramificationIdx' P * (span {(p : ℤ)}).inertiaDeg' P = 1) :
    (IsDedekindDomain.primesOverFinset (span {(p : ℤ)}) (𝓞 K)).card = Module.finrank ℚ K := by
  rw [← sum_ef K p hp, Finset.sum_congr rfl h, Finset.sum_const, smul_eq_mul, mul_one]
end Formalism.MainNotions.J
