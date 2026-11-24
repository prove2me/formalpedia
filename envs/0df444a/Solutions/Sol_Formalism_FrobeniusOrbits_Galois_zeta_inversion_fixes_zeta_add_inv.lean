-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Galois.zeta_inversion_fixes_zeta_add_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:34:18.571706+00:00
-- url     : https://prove2.me/submissions/7135ed05-b7ca-41f4-8c1f-5d8b6774b363

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_pow_val_neg
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_galMap_zeta_inversion
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_apply_theta
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_one_val
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
theorem _root_.solution (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) :
    tau0 hqd h (ζ + ζ⁻¹) = ζ + ζ⁻¹ := by
  rw [apply_theta h.1, autToPow_tau0_eq_neg_one hqd h, Units.val_neg, Units.val_one, pow_val_neg h.1,
    pow_val_neg h.1.inv, inv_inv, one_val, pow_one, pow_one, add_comm]
end Formalism.FrobeniusOrbits.Galois
