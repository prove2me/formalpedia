-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.characterSumData.partner_inPhi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:00:09.228908+00:00
-- url     : https://prove2.me/submissions/3b106189-ff70-47ab-a7c9-29856ae56245

import Definitions.Def_Formalism_SizeWindowBrackets_FirstPrimeNeSecondPrime
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_PB_inPhi_iff
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_PB_not_inPhi_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset ArithmeticFunction
noncomputable section
namespace Formalism.LFunctionChainParameters.characterSumData
open Formalism Formalism.D5
namespace PB
section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
private theorem partner_fst_lemma (t : H) (g : E0 × H) : (partner t g).1.1 = 1 + g.1.1 := by
  simp [partner, cconj, topPl]
end
end PB
open PB
section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
end
section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
end
section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
end
section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
end
section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
end
section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
end
section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
end
section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
end
end Formalism.LFunctionChainParameters.characterSumData
end
end

set_option autoImplicit false
open Finset ArithmeticFunction
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.characterSumData
open Formalism Formalism.D5
open PB
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace Formalism.LFunctionChainParameters.characterSumData
theorem _root_.solution {g : E0 × H} (t : H) (hg : ¬ InPhi g) : InPhi (partner t g) := by
  rw [inPhi_iff, partner_fst_lemma, (not_inPhi_iff g).1 hg]
  decide
end Formalism.LFunctionChainParameters.characterSumData
