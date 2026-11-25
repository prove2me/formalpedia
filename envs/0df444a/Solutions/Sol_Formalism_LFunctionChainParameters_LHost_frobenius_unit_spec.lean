-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LHost.frobenius_unit_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:38:06.886408+00:00
-- url     : https://prove2.me/submissions/0cd81390-8dca-4c54-a252-6165213e9bde

import Definitions.Def_Formalism_SizeWindowBrackets_GaloisToProductIsIso
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_unitsMap_eq_one_iff
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_unitsMap_eq_unitOfCoprime_iff
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_isFrobUnit_iff
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_units_ext_modEq
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_exists_unit_crt

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
theorem _root_.solution : FrobUnitSpec := by
  intro N p hN hp
  have : NeZero N := ⟨hN⟩
  have hcop : (ordProj[p] N).Coprime (ordCompl[p] N) := (Nat.coprime_ordCompl hp hN).pow_left _
  have hex : ∃ w, IsFrobUnit N p w := by
    obtain ⟨u, hu1, hu2⟩ := exists_unit_crt (Nat.ordProj_mul_ordCompl_eq_self N p).symm hcop
      (Nat.ordProj_dvd N p) (Nat.ordCompl_dvd N p) 1 (ZMod.unitOfCoprime p (Nat.coprime_ordCompl hp hN))
    refine ⟨u, (isFrobUnit_iff p u).2 ⟨?_, ?_⟩⟩
    · exact (unitsMap_eq_unitOfCoprime_iff _ _ u).1 hu2
    · exact (unitsMap_eq_one_iff _ u).1 hu1
  have hspec : IsFrobUnit N p (frobUnit N p) := by
    unfold frobUnit
    rw [dif_pos hex]
    exact hex.choose_spec
  refine ⟨hspec, fun w hw => ?_⟩
  rw [isFrobUnit_iff] at hspec hw
  apply units_ext_modEq
  have h1 := hw.1.trans hspec.1.symm
  have h2 := hw.2.trans hspec.2.symm
  have := (Nat.modEq_and_modEq_iff_modEq_mul hcop).1 ⟨h2, h1⟩
  rwa [Nat.ordProj_mul_ordCompl_eq_self] at this
end Formalism.LFunctionChainParameters.LHost
