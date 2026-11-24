-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.odd_smul_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:50:10.654425+00:00
-- url     : https://prove2.me/submissions/6ac335c6-44cc-46fb-8208-e66939fa2ffe

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
import Definitions.Def_Formalism_TameInertiaTowers_InvLength
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_NormalOrderTwoCentral
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_OddEqOneOfSubOneMem
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_coe_smul
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_sgn_spec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal
noncomputable section
open Formalism Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.TwoAdicCyclotomicDecomposition
theorem _root_.solution {L : Type} [Field L] [NumberField L] (σ : Gal(L/ℚ)) (x : L) (c : ℤ)
    (hx : x ^ 2 = (c : L)) (X : 𝓞 L) (hX : (X : L) = x) :
    σ • X = (((sgn σ x : ℤˣ) : ℤ) : 𝓞 L) * X := by
  apply RingOfIntegers.coe_injective
  show ((σ • X : 𝓞 L) : L) = ((((sgn σ x : ℤˣ) : ℤ) : 𝓞 L) * X : 𝓞 L)
  rw [odd_coe_smul, hX, odd_sgn_spec σ x c hx]
  simp [hX]
end Formalism.TwoAdicCyclotomicDecomposition
