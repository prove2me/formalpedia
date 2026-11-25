-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LHost.cosetMean_chC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:33:21.621075+00:00
-- url     : https://prove2.me/submissions/ebda77e5-e9b9-4b06-b372-8089f6ac2483

import Definitions.Def_Formalism_SizeWindowBrackets_GaloisToProductIsIso
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_cosetMean_of_trivial
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_cosetMean_of_nontrivial
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_hostN_ne_zero
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_HostHyp_ne
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_jac_two_d
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_jac_q_d
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_recMap_of_modEq
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_unitOfCoprime_modEq
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_host_unram
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_host_frob_two
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_host_frob_q
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_coprime_hostN
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_chC_val
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_chC_trivial_two
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_chC_trivial_q
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_chC_nontrivial_d
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_jac_self

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
variable {e q d : ℕ} [Fact q.Prime] [Fact d.Prime]
namespace Formalism.LFunctionChainParameters.LHost
theorem _root_.solution (h : HostHyp q d) (p i : ℕ) (hp : p.Prime) (hi : i ≠ 0) :
    cosetMean ((hostData e q d).inertia p) (i • (hostData e q d).frob p) chC
      = (((jacobiSym (p : ℤ) d) ^ i : ℤ) : ℂ) := by
  have : NeZero (hostN e q d) := ⟨hostN_ne_zero e h⟩
  obtain ⟨hq2, hd2, hqd⟩ := HostHyp_ne h
  by_cases hpd : p = d
  · subst hpd
    rw [cosetMean_of_nontrivial _ _ _ (chC_nontrivial_d h), jac_self p hp.one_lt, zero_pow hi]
    simp
  by_cases hp2 : p = 2
  · subst hp2
    rw [cosetMean_of_trivial _ _ _ (chC_trivial_two h), AddChar.map_nsmul_eq_pow, host_frob_two h, jac_two_d h, chC_val]
    simp [sg]
  by_cases hpq : p = q
  · subst hpq
    have cq : p.Coprime (2 ^ (e + 2)) := Nat.Coprime.pow_right _ ((Nat.coprime_primes h.1 Nat.prime_two).2 hq2)
    rw [cosetMean_of_trivial _ _ _ (chC_trivial_q h), AddChar.map_nsmul_eq_pow, host_frob_q h cq, jac_q_d h, chC_val]
    simp
  have hcop := coprime_hostN e h hp hp2 hpq hpd
  obtain ⟨h1, h2⟩ := host_unram (e := e) h p hcop hp
  have c2 : p.Coprime (2 ^ (e + 2)) := Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  rw [cosetMean_of_trivial _ _ _ (by
      intro x hx
      rw [h1, AddSubgroup.mem_bot] at hx
      rw [hx, AddChar.map_zero_eq_one]), AddChar.map_nsmul_eq_pow, h2,
    recMap_of_modEq _ p p p c2 (unitOfCoprime_modEq hcop (d_dvd_hostN e q d))
      (unitOfCoprime_modEq hcop (q_dvd_hostN e q d)) (unitOfCoprime_modEq hcop (two_dvd_hostN e q d)), chC_val]
  have hJ : jacobiSym (p : ℤ) d = 1 ∨ jacobiSym (p : ℤ) d = -1 := by
    apply jacobiSym.eq_one_or_neg_one
    rw [Int.gcd_natCast_natCast]
    exact (Nat.coprime_primes hp h.2.1).2 hpd
  rcases hJ with hJ | hJ <;> rw [hJ] <;> simp
end Formalism.LFunctionChainParameters.LHost
