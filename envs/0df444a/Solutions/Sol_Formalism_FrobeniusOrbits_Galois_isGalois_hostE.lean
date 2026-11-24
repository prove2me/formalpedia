-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Galois.isGalois_hostE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:42:11.254852+00:00
-- url     : https://prove2.me/submissions/67a4e553-2b6a-4e2c-9876-b888c6013d87

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_gal_mul_comm_of_isLayer
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_hostE_eq_fixedField

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
    IsGalois ℚ (hostE ζ a b) := by
  haveI := (layer_galois hqd h).1
  haveI : (Subgroup.zpowers (tau0 hqd h)).Normal :=
    ⟨fun n hn g => by rwa [gal_mul_comm_of_isLayer hqd h g n, mul_inv_cancel_right]⟩
  rw [hostE_eq_fixedField hqd h]
  exact IsGalois.of_fixedField_normal_subgroup _
end Formalism.FrobeniusOrbits.Galois
