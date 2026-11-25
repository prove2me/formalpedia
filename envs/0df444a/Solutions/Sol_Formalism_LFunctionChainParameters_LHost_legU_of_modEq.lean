-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LHost.legU_of_modEq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:58:36.468858+00:00
-- url     : https://prove2.me/submissions/8a6496d8-f99e-4972-8bdc-97da32249bea

import Definitions.Def_Formalism_SizeWindowBrackets_GaloisToProductIsIso
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_cast_eq_natCast_iff

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
theorem _root_.solution {N l : ℕ} [NeZero N] [Fact l.Prime] (h : l ∣ N) (u : (ZMod N)ˣ) (k : ℕ)
    (hk : (u : ZMod N).val ≡ k [MOD l]) : ((legU N l h u : ℤˣ) : ℤ) = jacobiSym (k : ℤ) l := by
  unfold legU
  rw [MonoidHom.comp_apply, MulChar.coe_toUnitHom, ZMod.unitsMap_val, (cast_eq_natCast_iff _ _ _).2 hk,
    ← jacobiSym.legendreSym.to_jacobiSym, legendreSym, Int.cast_natCast]
end Formalism.LFunctionChainParameters.LHost
