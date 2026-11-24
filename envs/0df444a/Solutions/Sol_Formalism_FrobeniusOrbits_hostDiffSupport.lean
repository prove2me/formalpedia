-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.hostDiffSupport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:55:53.284916+00:00
-- url     : https://prove2.me/submissions/6afa00ce-f681-492b-9c8b-2d108f2255d9

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostDiffSupport
import Definitions.Def_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Principal
import Theorems.Thm_Formalism_FrobeniusOrbits_Principal_inertia_trivial
import Theorems.Thm_Formalism_FrobeniusOrbits_HostHyp_toHypOdd
import Theorems.Thm_Formalism_FrobeniusOrbits_hostE_isGalois
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_HypQD_toHypOdd


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
namespace Formalism.FrobeniusOrbits
theorem _root_.solution : HostDiffSupport := by
  intro e q d hH L _ _ ζ a b h P hP hdvd
  have hqd := hH.toHypOdd
  by_contra hcon
  push Not at hcon
  obtain ⟨h2, hq⟩ := hcon
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    have := differentIdeal_ne_bot (A := 𝓞 (KinE ζ a b)) (B := 𝓞 (hostE ζ a b))
    exact this (by rwa [← Ideal.zero_eq_bot, zero_dvd_iff] at hdvd)
  have hEgal : IsGalois ℚ (hostE ζ a b) := hostE_isGalois hqd h
  have hKgal : IsGalois (KinE ζ a b) (hostE ζ a b) := IsGalois.tower_top_of_isGalois ℚ _ _
  have : IsGaloisGroup (hostE ζ a b ≃ₐ[KinE ζ a b] hostE ζ a b) (𝓞 (KinE ζ a b))
      (𝓞 (hostE ζ a b)) := IsGaloisGroup.of_isFractionRing _ _ _ (KinE ζ a b) (hostE ζ a b)
  have hpr : (P.under (𝓞 (KinE ζ a b))).IsPrime := Ideal.IsPrime.under _ P
  have hcard := card_inertia_eq_ramificationIdxIn (G := hostE ζ a b ≃ₐ[KinE ζ a b] hostE ζ a b)
    (P.under (𝓞 (KinE ζ a b))) P
  rw [ramificationIdxIn_eq_ramificationIdx (P.under (𝓞 (KinE ζ a b))) P
    (hostE ζ a b ≃ₐ[KinE ζ a b] hostE ζ a b)] at hcard
  have h1 : Nat.card (P.inertia (hostE ζ a b ≃ₐ[KinE ζ a b] hostE ζ a b)) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun x y => Subtype.ext ?_⟩, ⟨⟨1, one_mem _⟩⟩⟩
    rw [inertia_trivial hH h P hP0 h2 hq x.1 (AddSubgroup.mem_inertia.mp x.2),
      inertia_trivial hH h P hP0 h2 hq y.1 (AddSubgroup.mem_inertia.mp y.2)]
  rw [h1] at hcard
  exact (dvd_differentIdeal_iff.mp hdvd) ((Ideal.ramificationIdx_eq_one_iff).mp hcard.symm)
end Formalism.FrobeniusOrbits
