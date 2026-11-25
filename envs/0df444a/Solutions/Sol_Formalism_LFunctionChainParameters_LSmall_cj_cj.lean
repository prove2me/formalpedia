-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LSmall.cj_cj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:16:40.36681+00:00
-- url     : https://prove2.me/submissions/008689f4-dc2f-4af7-a68b-5bcfee40eede

import Definitions.Def_Formalism_SizeWindowBrackets_SSmall
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PSmall
import Theorems.Thm_Formalism_LFunctionChainParameters_LSmall_cj_apply

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
theorem _root_.solution {m n : Type} (M : Matrix m n ℂ) : cj (cj M) = M := by
  ext i j; simp [cj_apply]
end Formalism.LFunctionChainParameters.LSmall
