-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Galois.pow_val_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:14:10.768166+00:00
-- url     : https://prove2.me/submissions/d4943696-2041-4276-ba58-7f295c98cc2e

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_pow_val_mul_eq_one_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.Galois
variable {K : Type*} [Field K] {N : ℕ} [NeZero N] {ζ : K}
namespace Formalism.FrobeniusOrbits.Galois
theorem _root_.solution (hζ : IsPrimitiveRoot ζ N) (k : ZMod N) :
    ζ ^ (-k).val = ζ⁻¹ ^ k.val := by
  rw [inv_pow]
  exact eq_inv_of_mul_eq_one_left ((pow_val_mul_eq_one_iff hζ (-k) k).2 (by ring))
end Formalism.FrobeniusOrbits.Galois
