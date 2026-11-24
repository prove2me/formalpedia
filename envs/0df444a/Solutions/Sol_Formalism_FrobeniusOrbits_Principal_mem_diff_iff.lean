-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Principal.mem_diff_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:26:08.688742+00:00
-- url     : https://prove2.me/submissions/1dfae464-6ad8-4b3a-a28e-28f728f97f0f

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostDiffSupport
import Definitions.Def_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Principal
import Theorems.Thm_Formalism_FrobeniusOrbits_Principal_one_ne
import Theorems.Thm_Formalism_FrobeniusOrbits_Principal_mem_dual_iff
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_key


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise nonZeroDivisors
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Principal
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
open Formalism.FrobeniusOrbits.Principal
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
namespace Formalism.FrobeniusOrbits.Principal
theorem _root_.solution (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) (z : 𝓞 (hostE ζ a b)) :
    z ∈ differentIdeal (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) ↔
      ∀ y : (hostE ζ a b), (∀ x : 𝓞 (hostE ζ a b), IsIntegral ℤ (∑ τ : (hostE ζ a b) ≃ₐ[KinE ζ a b] (hostE ζ a b), τ (y * x))) →
        IsIntegral ℤ ((z : (hostE ζ a b)) * y) := by
  have key : ∀ w : hostE ζ a b,
      w ∈ (1 : FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b)) ↔ IsIntegral ℤ w := by
    intro w
    rw [FractionalIdeal.mem_one_iff]
    constructor
    · rintro ⟨w', rfl⟩
      exact w'.isIntegral_coe
    · intro hw
      exact ⟨⟨w, hw⟩, rfl⟩
  have hz : z ∈ differentIdeal (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) ↔
      (z : hostE ζ a b) ∈ ((differentIdeal (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) :
        FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b))) := by
    rw [FractionalIdeal.mem_coeIdeal]
    constructor
    · intro hz
      exact ⟨z, hz, rfl⟩
    · rintro ⟨z', hz', he⟩
      have he' : z' = z := IsFractionRing.injective (𝓞 (hostE ζ a b)) (hostE ζ a b) he
      rwa [he'] at hz'
  have hd0 : FractionalIdeal.dual (𝓞 (KinE ζ a b)) (KinE ζ a b)
      (1 : FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b)) ≠ 0 := by
    first
    | exact FractionalIdeal.dual_ne_zero (one_ne ζ a b)
    | exact FractionalIdeal.dual_ne_zero _ _ (one_ne ζ a b)
  rw [hz]
  first
  | rw [coeIdeal_differentIdeal (𝓞 (KinE ζ a b)) (KinE ζ a b) (hostE ζ a b) (𝓞 (hostE ζ a b))]
  | rw [coeIdeal_differentIdeal (𝓞 (KinE ζ a b)) (KinE ζ a b)]
  | rw [coeIdeal_differentIdeal]
  rw [FractionalIdeal.mem_inv_iff hd0]
  constructor
  · intro hmem y hy
    exact (key _).mp (hmem y ((mem_dual_iff hqd h y).mpr hy))
  · intro hmem y hy
    exact (key _).mpr (hmem y ((mem_dual_iff hqd h y).mp hy))
end Formalism.FrobeniusOrbits.Principal
