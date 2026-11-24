-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Galois.zeta_inversion_fixes_b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:22:15.186801+00:00
-- url     : https://prove2.me/submissions/13338a4f-09ec-439e-84ba-a99c95b2f14b

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_fix_of_sgn_one
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_galMap_zeta_inversion

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
theorem _root_.solution (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) : tau0 hqd h b = b := by
  apply fix_of_sgn_one
  have h1 := galMap_zeta_inversion hqd h
  rw [galMap.eq_1] at h1
  exact congrArg (fun g => g.2.2) h1
end Formalism.FrobeniusOrbits.Galois
