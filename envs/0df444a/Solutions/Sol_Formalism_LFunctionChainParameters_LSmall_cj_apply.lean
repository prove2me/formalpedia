-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LSmall.cj_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:57:27.233747+00:00
-- url     : https://prove2.me/submissions/db477607-c358-4238-85fb-6b8429af9234

import Definitions.Def_Formalism_SizeWindowBrackets_SSmall
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PSmall

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
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LSmall
open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds
open Matrix Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
namespace Formalism.LFunctionChainParameters.LSmall
theorem _root_.solution {m n : Type} (M : Matrix m n ℂ) (i : m) (j : n) : cj M i j = starRingEnd ℂ (M i j) := rfl
end Formalism.LFunctionChainParameters.LSmall
