-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LHost.primitive_value_ramified
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:58:38.000466+00:00
-- url     : https://prove2.me/submissions/de186974-89d7-4b72-adda-a256c1ee2d3d

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
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_primitive_value_pow


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
theorem _root_.solution : PrimValRamified H := by
  intro N q1 d r ψ p i hp hi
  rw [primitive_value_pow (cftData q1 d r) ψ p i hp hi]
  refine ⟨fun h => ?_, fun h => cosetMean_of_nontrivial _ _ _ h⟩
  rw [cosetMean_of_trivial _ _ _ h, AddChar.map_nsmul_eq_pow]
end Formalism.LFunctionChainParameters.LHost
