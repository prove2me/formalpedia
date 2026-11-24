-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Galois.zeta_inversion_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:32:19.029378+00:00
-- url     : https://prove2.me/submissions/74dac4c1-818a-4b96-a867-dca63609ada8

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_pow_val_eq_iff
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_galMap_zeta_inversion
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_two_lt
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_one_val
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_AdmissibleUnits_neg_one_ne_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField IntermediateField
noncomputable section
namespace Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
namespace Galois
section Roots
variable {K : Type*} [Field K] {N : ℕ} [NeZero N] {ζ : K}
end Roots
section Layer
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
private theorem autToPow_tau0_eq_neg_one (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) :
    h.1.autToPow ℚ (tau0 hqd h) = -1 := by
  have h1 := galMap_zeta_inversion hqd h
  rw [galMap.eq_1] at h1
  exact congrArg Prod.fst h1
end Layer
section Host
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
end Host
end Galois
open Galois
end Formalism.FrobeniusOrbits
end
end

set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.Galois
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
namespace Formalism.FrobeniusOrbits.Galois
theorem _root_.solution (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) : tau0 hqd h ≠ 1 := by
  intro h1
  haveI : Fact (2 < 2 ^ (e + 2)) := ⟨two_lt e⟩
  have hz := h.1.autToPow_spec ℚ (tau0 hqd h)
  rw [autToPow_tau0_eq_neg_one hqd h, h1, AlgEquiv.one_apply, Units.val_neg, Units.val_one] at hz
  have h2 : ζ ^ (-1 : ZMod (2 ^ (e + 2))).val = ζ ^ (1 : ZMod (2 ^ (e + 2))).val := by
    rw [hz, one_val, pow_one]
  exact ZMod.neg_one_ne_one ((pow_val_eq_iff h.1 _ _).1 h2)
end Formalism.FrobeniusOrbits.Galois
