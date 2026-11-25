-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LHost.exists_frob_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:09:40.952253+00:00
-- url     : https://prove2.me/submissions/c1c16ed1-3019-459a-aaf6-51e6005fd358

import Definitions.Def_Formalism_SizeWindowBrackets_GaloisToProductIsIso
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_HostHyp_ne
import Theorems.Thm_Formalism_FrobeniusOrbits_Decomp_omega_integral
import Theorems.Thm_Formalism_FrobeniusOrbits_HostHyp_toHypOdd
import Theorems.Thm_Formalism_FrobeniusOrbits_Inertia_omega_integral
import Theorems.Thm_Formalism_FrobeniusOrbits_hostDecomp
import Theorems.Thm_Formalism_FrobeniusOrbits_hostFrob_of
import Theorems.Thm_Formalism_FrobeniusOrbits_hostGalSpec
import Theorems.Thm_Formalism_FrobeniusOrbits_hostGalois
import Theorems.Thm_Formalism_FrobeniusOrbits_hostInertia
import Theorems.Thm_Formalism_FrobeniusOrbits_mem_Psi_iff
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_HypQD_toHypOdd
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_layerGalois
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_card_under
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_cyc_frob
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_frob_sgn
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_intCast_mem_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LHost
open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData
open Formalism.FrobeniusOrbits (HostHyp HGrp hcl)
open NumberField Ideal
open Formalism.FrobeniusOrbits (hostE galE aE bE hostGalois hostGalSpec hostInertia hostDecomp hostFrob_of)
open Formalism.TwoAdicCyclotomicDecomposition (IsLayer galMap layerGalois odd_cyc_frob odd_frob_sgn odd_card_under odd_intCast_mem_iff)
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
variable [Fact q.Prime] [Fact d.Prime]
omit [Fact q.Prime] [Fact d.Prime]
namespace Formalism.LFunctionChainParameters.LHost
theorem _root_.solution (h : HostHyp q d) (hL : IsLayer (e + 2) q d ζ a b)
    (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] [hPl : P.LiesOver (span {((2 : ℕ) : ℤ)})] :
    ∃ σ₀ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b, IsArithFrobAt ℤ σ₀ P ∧ (galE e ζ a b σ₀).1 = (-1, 1) := by
  have hqd := h.toHypOdd
  obtain ⟨hq2, hd2, -⟩ := HostHyp_ne h
  obtain ⟨hEgal, -, -, -⟩ := hostGalois e q d hqd L ζ a b hL
  have := hEgal
  have : P.LiesOver (span {(2 : ℤ)}) := by simpa using hPl
  have : Finite (𝓞 (hostE ζ a b) ⧸ P) := by
    have hpb : span {(2 : ℤ)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      norm_num
    exact Ring.HasFiniteQuotients.finiteQuotient (Ideal.ne_bot_of_liesOver_of_ne_bot hpb P)
  obtain ⟨σ₀, h₀⟩ := IsArithFrobAt.exists_of_isInvariant ℤ Gal(hostE ζ a b/ℚ) P
  have cq : q.Coprime (2 ^ (e + 2)) := Nat.Coprime.pow_right _ ((Nat.coprime_primes h.1 Nat.prime_two).2 hq2)
  have cd : d.Coprime (2 ^ (e + 2)) := Nat.Coprime.pow_right _ ((Nat.coprime_primes h.2.1 Nat.prime_two).2 hd2)
  have hD := (hostDecomp e q d h L ζ a b hL (ZMod.unitOfCoprime q cq) (ZMod.unitOfCoprime d cd)
    (ZMod.coe_unitOfCoprime q cq) (ZMod.coe_unitOfCoprime d cd) σ₀).1 P
  have hb1 : (galE e ζ a b σ₀).1.2 = 1 := (FrobeniusOrbits.mem_Psi_iff _).1 (hD.1 h₀.mem_stabilizer)
  have ha1 : (galE e ζ a b σ₀).1.1 = -1 := by
    rcases Int.units_eq_one_or (galE e ζ a b σ₀).1.1 with h1 | h1
    · exfalso
      have hin : ∀ x : 𝓞 (hostE ζ a b), σ₀ • x - x ∈ P :=
        ((hostInertia e q d h L ζ a b hL σ₀).1 P).2 (Prod.ext h1 hb1)
      have hq8 : q % 8 = 3 := h.2.2.1
      have hq4 : q % 4 = 3 := by omega
      have haE : (aE ζ a b) ^ 2 = -(q : hostE ζ a b) := by
        apply Subtype.ext
        push_cast
        exact hL.2.1
      let W : 𝓞 (hostE ζ a b) := ⟨(1 + aE ζ a b) / 2, FrobeniusOrbits.Inertia.omega_integral hq4 haE⟩
      have hF := h₀ W
      rw [odd_card_under 2 P, MulSemiringAction.toAlgHom_apply] at hF
      have h3 : W ^ 2 - W ∈ P := by
        have := P.sub_mem (hin W) hF
        convert this using 1
        ring
      set c : ℤ := ((q : ℤ) + 1) / 4 with hc
      have h4 : 4 * c = (q : ℤ) + 1 := by omega
      have h4E : 4 * (c : hostE ζ a b) = (q : hostE ζ a b) + 1 := by exact_mod_cast h4
      have hW : W ^ 2 - W = ((-c : ℤ) : 𝓞 (hostE ζ a b)) := by
        apply RingOfIntegers.coe_injective
        simp only [map_sub, map_pow, map_intCast]
        change ((1 + aE ζ a b) / 2) ^ 2 - (1 + aE ζ a b) / 2 = ((-c : ℤ) : hostE ζ a b)
        push_cast
        linear_combination (1 / 4 : hostE ζ a b) * haE + (1 / 4 : hostE ζ a b) * h4E
      rw [hW, odd_intCast_mem_iff 2 P] at h3
      omega
    · exact h1
  exact ⟨σ₀, h₀, Prod.ext ha1 hb1⟩
end Formalism.LFunctionChainParameters.LHost
