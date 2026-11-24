-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Galois.hostE_le_fixedField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:02:31.326867+00:00
-- url     : https://prove2.me/submissions/bd022f1d-9b8d-4c55-abda-9f496ace729e

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_zeta_inversion_fixes_zeta_add_inv
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_zeta_inversion_fixes_a
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_zeta_inversion_fixes_b
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_mem_fixedField_zpowers
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_hostE_eq_adjoin

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
    hostE ζ a b ≤ fixedField (Subgroup.zpowers (tau0 hqd h)) := by
  rw [hostE_eq_adjoin, IntermediateField.adjoin_le_iff]
  intro x hx
  rw [SetLike.mem_coe, mem_fixedField_zpowers]
  rcases hx with rfl | rfl | rfl
  · exact zeta_inversion_fixes_zeta_add_inv hqd h
  · exact zeta_inversion_fixes_a hqd h
  · exact zeta_inversion_fixes_b hqd h
end Formalism.FrobeniusOrbits.Galois
