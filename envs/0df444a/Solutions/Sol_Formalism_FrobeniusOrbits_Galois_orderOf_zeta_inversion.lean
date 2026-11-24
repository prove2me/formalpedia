-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Galois.orderOf_zeta_inversion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:25:58.566256+00:00
-- url     : https://prove2.me/submissions/c86ef9b3-a5d0-46de-a9dc-4476b881710e

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_zeta_inversion_ne_one
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_zeta_inversion_sq_eq_one

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
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
namespace Formalism.FrobeniusOrbits.Galois
theorem _root_.solution (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) :
    orderOf (tau0 hqd h) = 2 := by
  exact orderOf_eq_prime (zeta_inversion_sq_eq_one hqd h) (zeta_inversion_ne_one hqd h)
end Formalism.FrobeniusOrbits.Galois
