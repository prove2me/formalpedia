-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LHost.extension_data_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:17:52.150051+00:00
-- url     : https://prove2.me/submissions/8672dcbd-317f-47f3-aca9-8ba96d4bd8eb

import Definitions.Def_Formalism_SizeWindowBrackets_GaloisToProductIsIso
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_hostN_ne_zero
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_HostHyp_ne
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_jac_flip
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_recMap_of_modEq
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_unitOfCoprime_modEq
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_host_unram
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_host_inertia_two
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_host_inertia_q
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_host_inertia_d
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_host_frob_two
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_host_frob_q
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_host_frob_d
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_coprime_hostN
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_galois_map_apply
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_field_inertia
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_field_frob_of
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_exists_frob_odd
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_exists_frob_two
import Theorems.Thm_Formalism_FrobeniusOrbits_hostDecomp
import Theorems.Thm_Formalism_FrobeniusOrbits_hostFrob_of
import Theorems.Thm_Formalism_FrobeniusOrbits_hostGalSpec
import Theorems.Thm_Formalism_FrobeniusOrbits_hostGalois
import Theorems.Thm_Formalism_FrobeniusOrbits_hostInertia
import Theorems.Thm_Formalism_FrobeniusOrbits_hostRecip
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
namespace Formalism.LFunctionChainParameters.LHost
theorem _root_.solution : HostDataField := by
  intro e q d _ _ h L _ _ ζ a b hL p _ P _ _ σ
  refine ⟨field_inertia h hL p P σ, ?_⟩
  have hp : p.Prime := Fact.out
  obtain ⟨hq2, hd2, hqd⟩ := HostHyp_ne h
  by_cases hp2 : p = 2
  · subst hp2
    obtain ⟨σ₀, h₀, h1⟩ := exists_frob_two h hL P
    refine field_frob_of h hL 2 P σ₀ h₀ ?_ σ
    rw [host_inertia_two h, host_frob_two h, galois_map_apply, h1]
    simp [sg]
  obtain ⟨σ₀, h₀, hH, ha, hb⟩ := exists_frob_odd h hL p hp2 P
  have c2 : p.Coprime (2 ^ (e + 2)) := Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  refine field_frob_of h hL p P σ₀ h₀ ?_ σ
  rw [galois_map_apply, hH c2]
  by_cases hpq : p = q
  · subst hpq
    rw [hb hqd, h.2.2.2.2, host_frob_q h c2, host_inertia_q h]
    by_cases hs : (((galE e ζ a b σ₀).1.1 : ℤˣ) : ℤ) = 1 <;> simp [hs, sg]
  by_cases hpd : p = d
  · subst hpd
    rw [ha hqd.symm, FrobeniusOrbits.hostRecip q p h, host_frob_d h c2, host_inertia_d h]
    by_cases hs : (((galE e ζ a b σ₀).1.2 : ℤˣ) : ℤ) = 1 <;> simp [hs, sgc0]
  have : NeZero (hostN e q d) := ⟨hostN_ne_zero e h⟩
  have hcop := coprime_hostN e h hp hp2 hpq hpd
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hd4 : d % 4 = 3 := by have := h.2.2.2.1; omega
  have hq4 : q % 4 = 3 := by have := h.2.2.1; omega
  rw [ha hpq, hb hpd, (host_unram h p hcop hp).2,
    recMap_of_modEq _ p p p c2 (unitOfCoprime_modEq hcop (d_dvd_hostN e q d))
      (unitOfCoprime_modEq hcop (q_dvd_hostN e q d)) (unitOfCoprime_modEq hcop (two_dvd_hostN e q d)),
    jac_flip hd4 hodd, jac_flip hq4 hodd, sub_self]
  exact AddSubgroup.zero_mem _
end Formalism.LFunctionChainParameters.LHost
