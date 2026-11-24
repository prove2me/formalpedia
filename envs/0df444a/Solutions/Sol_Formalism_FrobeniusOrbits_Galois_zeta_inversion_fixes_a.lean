-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Galois.zeta_inversion_fixes_a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:39:43.2558+00:00
-- url     : https://prove2.me/submissions/bf140b70-7ca7-481a-9439-87f2435c65f1

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
theorem _root_.solution (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) : tau0 hqd h a = a := by
  apply fix_of_sgn_one
  have h1 := galMap_zeta_inversion hqd h
  rw [galMap.eq_1] at h1
  exact congrArg (fun g => g.2.1) h1
end Formalism.FrobeniusOrbits.Galois
