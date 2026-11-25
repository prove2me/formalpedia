-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LHost.extension_local_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:43:03.306339+00:00
-- url     : https://prove2.me/submissions/70ef7394-ac34-456c-b355-327291ebd968

import Definitions.Def_Formalism_SizeWindowBrackets_GaloisToProductIsIso
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_parts_of_eq
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_HostHyp_ne

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
theorem _root_.solution : HostLocalParts := by
  intro e q d h
  obtain ⟨hq2, hd2, hqd⟩ := HostHyp_ne h
  have hq := h.1
  have hd := h.2.1
  have h2q : ¬ 2 ∣ q := fun hh => hq2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).1 hh).symm
  have h2d : ¬ 2 ∣ d := fun hh => hd2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hd).1 hh).symm
  have hq2' : ¬ q ∣ 2 ^ (e + 2) := fun hh =>
    hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow hh))
  have hd2' : ¬ d ∣ 2 ^ (e + 2) := fun hh =>
    hd2 ((Nat.prime_dvd_prime_iff_eq hd Nat.prime_two).1 (hd.dvd_of_dvd_pow hh))
  have hqd' : ¬ q ∣ d := fun hh => hqd ((Nat.prime_dvd_prime_iff_eq hq hd).1 hh)
  have hdq' : ¬ d ∣ q := fun hh => hqd ((Nat.prime_dvd_prime_iff_eq hd hq).1 hh).symm
  have hp0 : (2 : ℕ) ^ (e + 2) ≠ 0 := pow_ne_zero _ two_ne_zero
  refine ⟨?_, ?_, ?_⟩
  · exact parts_of_eq Nat.prime_two (by unfold hostN; ring)
      (fun hh => (Nat.prime_two.dvd_mul.1 hh).elim h2q h2d) (Nat.mul_ne_zero hq.ne_zero hd.ne_zero)
  · have := parts_of_eq (N := hostN e q d) (k := 1) (m := 2 ^ (e + 2) * d) hq (by unfold hostN; ring)
      (fun hh => (hq.dvd_mul.1 hh).elim hq2' hqd') (Nat.mul_ne_zero hp0 hd.ne_zero)
    rwa [pow_one] at this
  · have := parts_of_eq (N := hostN e q d) (k := 1) (m := 2 ^ (e + 2) * q) hd (by unfold hostN; ring)
      (fun hh => (hd.dvd_mul.1 hh).elim hd2' hdq') (Nat.mul_ne_zero hp0 hq.ne_zero)
    rwa [pow_one] at this
end Formalism.LFunctionChainParameters.LHost
