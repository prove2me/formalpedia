-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Eta.ncard_eq_two_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:40:05.656379+00:00
-- url     : https://prove2.me/submissions/95ed1435-87bd-4824-aa32-538155113b18

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_NcardEqTwoIff
import Theorems.Thm_Formalism_FrobeniusOrbits_Eta_cases
import Theorems.Thm_Formalism_FrobeniusOrbits_Eta_card_gal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.Eta
variable (K : Type) [Field K] [NumberField K] [IsCMField K]
local notation3 "K⁺" => maximalRealSubfield K
namespace Formalism.FrobeniusOrbits.Eta
theorem _root_.solution
    (hunr : ∀ P : Ideal (𝓞 K), P.IsPrime → P ≠ ⊥ →
      ¬ ∀ x : 𝓞 K, IsCMField.complexConj K • x - x ∈ P)
    (P : Ideal (𝓞 K)) [P.IsPrime] (hP0 : P ≠ ⊥) :
    (primesOver (P.under (𝓞 K⁺)) (𝓞 K)).ncard = 2 ↔ IsCMField.complexConj K • P ≠ P := by
  classical
  have h1 := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (P.under (𝓞 K⁺)) (𝓞 K) (K ≃ₐ[K⁺] K)
  have h2 := Ideal.card_stabilizer_eq (G := K ≃ₐ[K⁺] K) (P.under (𝓞 K⁺)) P
  rw [← h2, card_gal K] at h1
  have hmem : ∀ g : K ≃ₐ[K⁺] K, g ∈ MulAction.stabilizer (K ≃ₐ[K⁺] K) P ↔ g • P = P :=
    fun g => MulAction.mem_stabilizer_iff
  constructor
  · intro h hcP
    have hne : MulAction.stabilizer (K ≃ₐ[K⁺] K) P ≠ ⊥ := by
      intro hb
      have hc : IsCMField.complexConj K ∈ MulAction.stabilizer (K ≃ₐ[K⁺] K) P := (hmem _).mpr hcP
      rw [hb, Subgroup.mem_bot] at hc
      exact IsCMField.complexConj_ne_one K hc
    have h3 : Nat.card (MulAction.stabilizer (K ≃ₐ[K⁺] K) P) ≠ 1 :=
      fun h' => hne (Subgroup.card_eq_one.mp h')
    rw [h] at h1
    omega
  · intro hcP
    have hb : MulAction.stabilizer (K ≃ₐ[K⁺] K) P = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro g hg
      rcases cases K g with hg1 | hg1
      · exact hg1
      · exfalso
        apply hcP
        rw [← hg1]
        exact (hmem g).mp hg
    rw [hb, Subgroup.card_bot, mul_one] at h1
    exact h1
end Formalism.FrobeniusOrbits.Eta
