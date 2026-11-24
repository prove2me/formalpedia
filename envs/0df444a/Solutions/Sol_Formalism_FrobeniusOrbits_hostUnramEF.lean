-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.hostUnramEF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:04:54.704958+00:00
-- url     : https://prove2.me/submissions/abbf2eac-0fea-4a60-be15-83981a8ef930

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Theorems.Thm_P2M_Formalism_FrobeniusOrbits_Inertia_neg_one_ne_one__f153e1d875d4
import Theorems.Thm_Formalism_FrobeniusOrbits_Inertia_sign_one
import Theorems.Thm_Formalism_FrobeniusOrbits_HostHyp_toHypOdd
import Theorems.Thm_Formalism_FrobeniusOrbits_hostGalSpec
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
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition Formalism.FrobeniusOrbits.Galois
open Inertia
namespace Formalism.FrobeniusOrbits
theorem _root_.solution : HostUnramEF := by
  intro e q d hH L _ _ ζ a b h P hP hP0 σ hσ hall
  have hqd := hH.toHypOdd
  have hq4 : q % 4 = 3 := by have := hH.2.2.1; omega
  have hd4 : d % 4 = 3 := by have := hH.2.2.2.1; omega
  have hspec := hostGalSpec e q d hqd L ζ a b h σ
  have hI0 : P.under ℤ ≠ ⊥ := fun h0 => hP0 (Ideal.eq_bot_of_comap_eq_bot h0)
  haveI : (P.under ℤ).IsPrime := by haveI := hP; exact Ideal.comap_isPrime _ _
  haveI := hP
  set g := Submodule.IsPrincipal.generator (P.under ℤ) with hgdef
  have hgspan : Ideal.span {g} = P.under ℤ := Submodule.IsPrincipal.span_singleton_generator _
  have hg0 : g ≠ 0 := by
    intro h0
    apply hI0
    rw [← hgspan, h0, Ideal.span_singleton_eq_bot.2 rfl]
  have hgp : Prime g := (Ideal.span_singleton_prime hg0).1 (by rw [hgspan]; infer_instance)
  have hp : g.natAbs.Prime := Int.prime_iff_natAbs_prime.1 hgp
  haveI : P.LiesOver (span {((g.natAbs : ℕ) : ℤ)}) :=
    ⟨(Ideal.span_singleton_eq_span_singleton.2 (Int.associated_natAbs g).symm).trans hgspan⟩
  by_cases hpq : g.natAbs = q
  · have hs := sign_one (bE ζ a b) ((galE e ζ a b σ).1.2) σ hspec.2.1 hqd.2.1 hd4 h.2.2.1 hp
      (by rw [hpq]; exact hqd.2.2.1) P hall
    rw [hσ] at hs
    exact neg_one_ne_one' hs
  · have hs := sign_one (aE ζ a b) ((galE e ζ a b σ).1.1) σ hspec.1 hqd.1 hq4 h.2.1 hp hpq P hall
    rw [hσ] at hs
    exact neg_one_ne_one' hs
end Formalism.FrobeniusOrbits
