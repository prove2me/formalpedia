-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LHost.inertia_conductor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:11:15.564619+00:00
-- url     : https://prove2.me/submissions/b7045af3-8d5b-4dd8-a0cd-73469fb3ae96

import Definitions.Def_Formalism_SizeWindowBrackets_GaloisToProductIsIso
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_trivial_on_inertia_iff

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
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace Formalism.LFunctionChainParameters.LHost
theorem _root_.solution : InertiaConductor H := by
  intro N q1 d r ψ p hN hp
  have : NeZero N := ⟨hN⟩
  rw [trivial_on_inertia_iff]
  constructor
  · intro h hpc
    exact Nat.not_dvd_ordCompl hp hN (hpc.trans h)
  · intro h
    exact Nat.dvd_ordCompl_of_dvd_not_dvd (DirichletCharacter.conductor_dvd_level _) h
end Formalism.LFunctionChainParameters.LHost
