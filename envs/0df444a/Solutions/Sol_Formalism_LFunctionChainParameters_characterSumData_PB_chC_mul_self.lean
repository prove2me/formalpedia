-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.characterSumData.PB.chC_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:30:47.285799+00:00
-- url     : https://prove2.me/submissions/9ac2aefc-0010-4214-932d-10b95013a09e

import Definitions.Def_Formalism_SizeWindowBrackets_FirstPrimeNeSecondPrime
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_PB_chC_sq
import Theorems.Thm_Formalism_D5_Bal_chC_sq

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
private theorem zero_apply_lemma (g : E0 × H) : (0 : AddChar (E0 × H) ℂ) g = 1 := by
  first
  | exact AddChar.zero_apply g
  | rfl
  | simp
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
open Formalism.LFunctionChainParameters.characterSumData.PB
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace Formalism.LFunctionChainParameters.characterSumData.PB
theorem _root_.solution : (chC : AddChar (E0 × H) ℂ) * chC = 0 := by
  ext g
  rw [AddChar.mul_apply, chC_sq, zero_apply_lemma]
end Formalism.LFunctionChainParameters.characterSumData.PB
