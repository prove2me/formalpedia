-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LHost.character_conductor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:17:48.197396+00:00
-- url     : https://prove2.me/submissions/2fb9ed43-5616-4f24-8b97-f310f460c636

import Definitions.Def_Formalism_SizeWindowBrackets_GaloisToProductIsIso
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_inertia_conductor
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_hostN_ne_zero
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_chC_trivial_two
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_chC_trivial_q
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_chC_nontrivial_d
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_cosetMean_chC

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
namespace Formalism.LFunctionChainParameters.LHost
theorem _root_.solution : ChConductor := by
  intro e q d _ _ h
  have hN := hostN_ne_zero e h
  constructor
  · have i2 := (inertia_conductor (H := HA e) (hostN e q d) q d (recMap e q d) chC 2 hN Nat.prime_two).1
      (chC_trivial_two h)
    have iq := (inertia_conductor (H := HA e) (hostN e q d) q d (recMap e q d) chC q hN h.1).1
      (chC_trivial_q h)
    have id : d ∣ (dirChar (recMap e q d) chC).conductor := by
      by_contra hh
      exact chC_nontrivial_d h
        ((inertia_conductor (H := HA e) (hostN e q d) q d (recMap e q d) chC d hN h.2.1).2 hh)
    have hdvd : (dirChar (recMap e q d) chC).conductor ∣ 2 ^ (e + 2) * q * d :=
      DirichletCharacter.conductor_dvd_level _
    have c2 : ((dirChar (recMap e q d) chC).conductor).Coprime (2 ^ (e + 2)) :=
      Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 i2).symm
    have cq : ((dirChar (recMap e q d) chC).conductor).Coprime q :=
      ((Nat.Prime.coprime_iff_not_dvd h.1).2 iq).symm
    exact Nat.dvd_antisymm (Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.mul_right c2 cq) hdvd) id
  · intro n hn
    let φ : ℤ →* ℤ :=
      { toFun := fun a => jacobiSym a d
        map_one' := jacobiSym.one_left d
        map_mul' := fun a b => jacobiSym.mul_left a b d }
    have hφ : jacobiSym (n : ℤ) d = ∏ p ∈ n.primeFactors, (jacobiSym (p : ℤ) d) ^ n.factorization p := by
      conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
      rw [Nat.prod_factorization_eq_prod_primeFactors, Nat.cast_prod]
      change φ _ = _
      rw [map_prod]
      apply Finset.prod_congr rfl
      intro p _
      rw [Nat.cast_pow, map_pow]
      rfl
    rw [hφ, Int.cast_prod]
    unfold primVal
    apply Finset.prod_congr rfl
    intro p hp
    have hi : n.factorization p ≠ 0 := by
      have := (Nat.support_factorization n ▸ hp : p ∈ n.factorization.support)
      exact Finsupp.mem_support_iff.1 this
    exact cosetMean_chC h p _ (Nat.prime_of_mem_primeFactors hp) hi
end Formalism.LFunctionChainParameters.LHost
