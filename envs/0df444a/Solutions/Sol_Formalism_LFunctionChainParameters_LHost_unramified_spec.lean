-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LHost.unramified_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:19:37.01465+00:00
-- url     : https://prove2.me/submissions/03536bbd-2fe1-419d-a6e2-c05cd56a9cec

import Definitions.Def_Formalism_SizeWindowBrackets_GaloisToProductIsIso
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_cast_eq_one_iff
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_mem_localUnits_iff
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_units_ext_modEq
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_frobUnit_modEq

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
namespace Formalism.LFunctionChainParameters.LHost
theorem _root_.solution : UnramSpec := by
  intro N p hN hp hpN
  have : NeZero N := ⟨hN⟩
  have hM : ordCompl[p] N = N := (Nat.ordCompl_eq_self_iff_zero_or_not_dvd N hp).2 (Or.inr hpN)
  constructor
  · rw [eq_bot_iff]
    intro u hu
    rw [mem_localUnits_iff, hM] at hu
    rw [Subgroup.mem_bot]
    apply units_ext_modEq
    refine hu.trans ?_
    have : ((1 : (ZMod N)ˣ) : ZMod N).val ≡ 1 [MOD N] := by
      rw [← cast_eq_one_iff]; simp
    exact this.symm
  · have h := (frobUnit_modEq (N := N) hp).1
    rw [hM] at h
    have := (ZMod.natCast_eq_natCast_iff _ _ N).2 h
    simpa using this
end Formalism.LFunctionChainParameters.LHost
