-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Eta.split_or_inert
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:40:07.171989+00:00
-- url     : https://prove2.me/submissions/f036baa9-3a16-4800-ab7d-6d54c56d6f53

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
    (𝔭 : Ideal (𝓞 K⁺)) [𝔭.IsPrime] (h𝔭 : 𝔭 ≠ ⊥) :
    (primesOver 𝔭 (𝓞 K)).ncard = 2 ∨
      ((primesOver 𝔭 (𝓞 K)).ncard = 1 ∧ 𝔭.inertiaDegIn (𝓞 K) = 2) := by
  classical
  have hmax : 𝔭.IsMaximal := Ideal.IsPrime.isMaximal inferInstance h𝔭
  obtain ⟨P, hPp, hPl⟩ : ∃ P : Ideal (𝓞 K), P.IsPrime ∧ P.LiesOver 𝔭 := by
    first
    | exact Ideal.nonempty_primesOver (S := 𝓞 K) 𝔭
    | (obtain ⟨Q, hQ⟩ := Ideal.nonempty_primesOver (S := 𝓞 K) 𝔭; exact ⟨Q, hQ.1, hQ.2⟩)
    | (obtain ⟨Q, hQm, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral 𝔭
          (S := 𝓞 K) (by
            rw [(RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective _ _)]
            exact bot_le)
       exact ⟨Q, hQm.isPrime, ⟨hQ.symm⟩⟩)
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot h𝔭 P
  have hin : P.inertia (K ≃ₐ[K⁺] K) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro g hg
    rcases cases K g with h | h
    · exact h
    · exfalso
      subst h
      exact hunr P hPp hP0 (fun x => hg x)
  have h1 := Ideal.ncard_primesOver_mul_card_inertia_mul_finrank (G := K ≃ₐ[K⁺] K) 𝔭 P
  rw [hin, Subgroup.card_bot, mul_one, card_gal K] at h1
  rw [Ideal.inertiaDegIn_eq_inertiaDeg 𝔭 P (K ≃ₐ[K⁺] K)]
  have hfpos : 0 < P.inertiaDeg (𝓞 K⁺) := Ideal.inertiaDeg_pos P (𝓞 K⁺)
  generalize (𝔭.primesOver (𝓞 K)).ncard = n at h1 ⊢
  generalize P.inertiaDeg (𝓞 K⁺) = f at h1 hfpos ⊢
  have hn : n ≤ 2 := by nlinarith
  interval_cases n
  · omega
  · right; exact ⟨rfl, by omega⟩
  · left; rfl
end Formalism.FrobeniusOrbits.Eta
