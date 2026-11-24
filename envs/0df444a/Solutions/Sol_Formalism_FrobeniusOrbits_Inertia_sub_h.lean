-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Inertia.sub_h
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:43:51.304151+00:00
-- url     : https://prove2.me/submissions/8945e033-9a39-4402-b8f1-d02fb70f7a1c

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Theorems.Thm_Formalism_FrobeniusOrbits_Inertia_mem_of_lift
import Theorems.Thm_Formalism_FrobeniusOrbits_Inertia_hcl_eq_one
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_galE_lift


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition Formalism.FrobeniusOrbits.Galois
open Formalism.FrobeniusOrbits.Inertia
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
namespace Formalism.FrobeniusOrbits.Inertia
theorem _root_.solution (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) (p : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})]
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (hσ : ∀ x : 𝓞 (hostE ζ a b), σ • x - x ∈ P) :
    (galE e ζ a b σ).2 = 1 := by
  haveI := (layer_galois hqd h).1
  have hinj : Function.Injective (algebraMap (𝓞 (hostE ζ a b)) (𝓞 L)) := by
    intro x y hxy
    have h1 := congrArg (fun z : 𝓞 L => (z : L)) hxy
    apply NumberField.RingOfIntegers.ext
    apply Subtype.ext
    exact h1
  obtain ⟨Q, -, hQp, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral P (⊥ : Ideal (𝓞 L))
    (by rw [Ideal.comap_bot_of_injective _ hinj]; exact bot_le)
  haveI := hQp
  haveI : Q.LiesOver P := ⟨hQc.symm⟩
  haveI : Q.LiesOver (span {(p : ℤ)}) := Ideal.LiesOver.trans Q P _
  set τ : Gal(L/ℚ) := σ.liftNormal L with hτ
  have hστ : ∀ x : hostE ζ a b, ((σ x : hostE ζ a b) : L) = τ x :=
    fun x => (σ.liftNormal_commutes L x).symm
  have hint : IsIntegral ℤ (thE ζ a b) := by
    have h0 : 0 < 2 ^ (e + 2) := by positivity
    have hL : IsIntegral ℤ (ζ + ζ⁻¹) := (h.1.isIntegral h0).add (h.1.inv.isIntegral h0)
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ (hostE ζ a b) L)
      (algebraMap (hostE ζ a b) L).injective).1 hL
  set θ : 𝓞 (hostE ζ a b) := ⟨thE ζ a b, hint⟩ with hθ
  rw [galE_lift h hστ]
  exact hcl_eq_one h p hp hp2 Q τ (algebraMap (𝓞 (hostE ζ a b)) (𝓞 L) θ) rfl
    (mem_of_lift P Q σ τ hστ hσ θ)
end Formalism.FrobeniusOrbits.Inertia
