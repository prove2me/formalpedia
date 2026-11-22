-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.odd_autToPow_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:24:38.909519+00:00
-- url     : https://prove2.me/submissions/23d71af8-1ada-4b44-a535-0102544cbece

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
import Definitions.Def_Formalism_TameInertiaTowers_InvLength
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_NormalOrderTwoCentral
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_OddEqOneOfSubOneMem

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
theorem _root_.solution {L : Type} [Field L] [NumberField L] {n : ℕ} {ζ : L}
    (hζ : IsPrimitiveRoot ζ (2 ^ n)) (σ : Gal(L/ℚ)) :
    σ • hζ.toInteger = hζ.toInteger ^ ((hζ.autToPow ℚ σ : ZMod (2 ^ n))).val := by
  apply RingOfIntegers.coe_injective
  rw [map_pow]
  exact (hζ.autToPow_spec ℚ σ).symm
end Formalism.TwoAdicCyclotomicDecomposition
