-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Galois.zeta_inversion_sq_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:02:33.245497+00:00
-- url     : https://prove2.me/submissions/aa2d3168-6c78-4683-93e9-c27d5ecda7a1

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_galMap_zeta_inversion
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_zeta_inversion_fixes_a
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_zeta_inversion_fixes_b
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
theorem _root_.solution (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) : tau0 hqd h ^ 2 = 1 := by
  apply (layer_galois hqd h).2.2.2.1
  have hA : (tau0 hqd h ^ 2) a = a := by rw [pow_two, AlgEquiv.mul_apply, zeta_inversion_fixes_a, zeta_inversion_fixes_a]
  have hB : (tau0 hqd h ^ 2) b = b := by rw [pow_two, AlgEquiv.mul_apply, zeta_inversion_fixes_b, zeta_inversion_fixes_b]
  have hU : h.1.autToPow ℚ (tau0 hqd h ^ 2) = h.1.autToPow ℚ 1 := by
    rw [map_pow, map_one, autToPow_tau0_eq_neg_one hqd h, neg_one_sq]
  rw [galMap.eq_1, galMap.eq_1, hU, sgn.eq_1, sgn.eq_1, sgn.eq_1, sgn.eq_1, if_pos hA, if_pos hB,
    if_pos (AlgEquiv.one_apply a), if_pos (AlgEquiv.one_apply b)]
end Formalism.FrobeniusOrbits.Galois
