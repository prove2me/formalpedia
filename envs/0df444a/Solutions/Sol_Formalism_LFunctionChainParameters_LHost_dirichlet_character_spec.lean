-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LHost.dirichlet_character_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:58:15.316163+00:00
-- url     : https://prove2.me/submissions/a7a41470-7cfa-468e-af86-ab403500ca4d

import Definitions.Def_Formalism_SizeWindowBrackets_GaloisToProductIsIso
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation

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
theorem _root_.solution : DirCharSpec H := by
  intro N r ψ
  refine ⟨fun u => ?_, fun x hx => MulChar.map_nonunit _ hx⟩
  unfold dirChar
  rw [MulChar.ofUnitHom_coe, MonoidHom.coe_toHomUnits]
  rfl
end Formalism.LFunctionChainParameters.LHost
