-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Principal.mem_dual_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:01:11.594693+00:00
-- url     : https://prove2.me/submissions/49af0ef1-1ef4-43f4-8c7c-a41967e10c70

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostDiffSupport
import Definitions.Def_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Principal
import Theorems.Thm_Formalism_FrobeniusOrbits_Principal_one_ne
import Theorems.Thm_Formalism_FrobeniusOrbits_hostE_isGalois


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
namespace Formalism.FrobeniusOrbits.Principal
theorem _root_.solution (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) (y : (hostE ζ a b)) :
    y ∈ FractionalIdeal.dual (𝓞 (KinE ζ a b)) (KinE ζ a b) (1 : FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b)) ↔
      ∀ x : 𝓞 (hostE ζ a b), IsIntegral ℤ (∑ τ : (hostE ζ a b) ≃ₐ[KinE ζ a b] (hostE ζ a b), τ (y * x)) := by
  haveI := hostE_isGalois hqd h
  haveI : IsGalois (KinE ζ a b) (hostE ζ a b) :=
    IsGalois.tower_top_of_isGalois ℚ (KinE ζ a b) (hostE ζ a b)
  have htr : ∀ w : hostE ζ a b, algebraMap (KinE ζ a b) (hostE ζ a b)
      (Algebra.trace (KinE ζ a b) (hostE ζ a b) w) =
      ∑ τ : (hostE ζ a b) ≃ₐ[KinE ζ a b] (hostE ζ a b), τ w :=
    fun w => by
      first
      | exact trace_eq_sum_automorphisms w
      | exact Algebra.trace_eq_sum_automorphisms w
      | exact IsGalois.trace_eq_sum_automorphisms w
  have hint : ∀ t : KinE ζ a b, IsIntegral ℤ (algebraMap (KinE ζ a b) (hostE ζ a b) t) ↔
      t ∈ (algebraMap (𝓞 (KinE ζ a b)) (KinE ζ a b)).range := by
    intro t
    rw [isIntegral_algebraMap_iff (algebraMap (KinE ζ a b) (hostE ζ a b)).injective]
    constructor
    · intro ht
      exact ⟨⟨t, ht⟩, rfl⟩
    · rintro ⟨s, rfl⟩
      exact s.isIntegral_coe
  rw [FractionalIdeal.mem_dual (one_ne ζ a b)]
  constructor
  · intro hy x
    have hx : ((x : hostE ζ a b)) ∈ (1 : FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b)) := by
      rw [FractionalIdeal.mem_one_iff]
      exact ⟨x, rfl⟩
    have h2 := hy _ hx
    rw [Algebra.traceForm_apply, ← hint, htr] at h2
    exact h2
  · intro hy w hw
    rw [FractionalIdeal.mem_one_iff] at hw
    obtain ⟨x, rfl⟩ := hw
    rw [Algebra.traceForm_apply, ← hint, htr]
    exact hy x
end Formalism.FrobeniusOrbits.Principal
