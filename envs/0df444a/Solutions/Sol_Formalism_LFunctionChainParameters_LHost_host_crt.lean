-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LHost.host_crt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:52:33.480222+00:00
-- url     : https://prove2.me/submissions/0eea06a3-cf26-4cfa-8d1f-4e613f751021

import Definitions.Def_Formalism_SizeWindowBrackets_GaloisToProductIsIso
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_exists_unit_crt
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
theorem _root_.solution (e : ℕ) {q d : ℕ} (h : HostHyp q d) (x2 : (ZMod (2 ^ (e + 2)))ˣ) (xq : (ZMod q)ˣ) (xd : (ZMod d)ˣ) :
    ∃ u : (ZMod (hostN e q d))ˣ, ZMod.unitsMap (two_dvd_hostN e q d) u = x2 ∧
      ZMod.unitsMap (q_dvd_hostN e q d) u = xq ∧ ZMod.unitsMap (d_dvd_hostN e q d) u = xd := by
  obtain ⟨hq2, hd2, hqd⟩ := HostHyp_ne h
  have c2q : (2 ^ (e + 2)).Coprime q :=
    Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two h.1).2 hq2.symm)
  have c2d : (2 ^ (e + 2)).Coprime d :=
    Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two h.2.1).2 hd2.symm)
  have cqd : q.Coprime d := (Nat.coprime_primes h.1 h.2.1).2 hqd
  obtain ⟨v, hv1, hv2⟩ := exists_unit_crt (N := 2 ^ (e + 2) * q) rfl c2q (dvd_mul_right _ _) (dvd_mul_left _ _) x2 xq
  have hA : 2 ^ (e + 2) * q ∣ hostN e q d := Dvd.intro _ rfl
  obtain ⟨u, hu1, hu2⟩ := exists_unit_crt (N := hostN e q d) (a := 2 ^ (e + 2) * q) (b := d) rfl
    (Nat.Coprime.mul_left c2d cqd) hA (d_dvd_hostN e q d) v xd
  refine ⟨u, ?_, ?_, hu2⟩
  · rw [← hv1, ← hu1, ← MonoidHom.comp_apply, ZMod.unitsMap_comp]
  · rw [← hv2, ← hu1, ← MonoidHom.comp_apply, ZMod.unitsMap_comp]
end Formalism.LFunctionChainParameters.LHost
