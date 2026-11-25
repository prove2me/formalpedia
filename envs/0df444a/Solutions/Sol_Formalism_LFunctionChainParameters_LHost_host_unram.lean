-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LHost.host_unram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:27:06.627252+00:00
-- url     : https://prove2.me/submissions/00d17d5c-72d4-48b4-8864-e35dc278eb9b

import Definitions.Def_Formalism_SizeWindowBrackets_GaloisToProductIsIso
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_unramified_spec
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_hostN_ne_zero
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_mem_host_inertia_iff

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
theorem _root_.solution (h : HostHyp q d) (p : ℕ) (hp : p.Coprime (hostN e q d)) (hpp : p.Prime) :
    (hostData e q d).inertia p = ⊥ ∧
      (hostData e q d).frob p = Multiplicative.toAdd (recMap e q d (ZMod.unitOfCoprime p hp)) := by
  have hN := hostN_ne_zero e h
  have hpN : ¬ p ∣ hostN e q d := fun hh => hpp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hp hh)
  obtain ⟨h1, h2⟩ := unramified_spec (hostN e q d) p hN hpp hpN
  constructor
  · rw [eq_bot_iff]
    intro x hx
    obtain ⟨u, hu, rfl⟩ := (mem_host_inertia_iff p x).1 hx
    rw [h1, Subgroup.mem_bot] at hu
    rw [hu, map_one]
    exact AddSubgroup.zero_mem _
  · change Multiplicative.toAdd (recMap e q d (frobUnit (hostN e q d) p)) = _
    congr 2
    apply Units.ext
    rw [h2, ZMod.coe_unitOfCoprime]
end Formalism.LFunctionChainParameters.LHost
