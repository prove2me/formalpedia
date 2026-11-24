-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Galois.finrank_cmField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:43:49.294599+00:00
-- url     : https://prove2.me/submissions/b916ccf4-24a5-427e-bc87-3f02bad268e2

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_orderOf_zeta_inversion
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
    Module.finrank ℚ (hostE ζ a b) = 2 ^ (e + 2) := by
  haveI := (layer_galois hqd h).1
  have hL := (layer_galois hqd h).2.1
  rw [hostE_eq_fixedField hqd h]
  have h1 := Module.finrank_mul_finrank ℚ (fixedField (Subgroup.zpowers (tau0 hqd h))) L
  rw [IntermediateField.finrank_fixedField_eq_card, hL] at h1
  simp only [Nat.card_zpowers, Fintype.card_zpowers, orderOf_zeta_inversion hqd h] at h1
  rw [pow_succ] at h1
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h1
end Formalism.FrobeniusOrbits.Galois
