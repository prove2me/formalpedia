-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.characterSumData.PB.chC_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:55:34.233861+00:00
-- url     : https://prove2.me/submissions/bfcdf0f9-0593-4bde-9f8e-4e7daba165f4

import Definitions.Def_Formalism_SizeWindowBrackets_FirstPrimeNeSecondPrime
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Theorems.Thm_P2M_Formalism_LFunctionChainParameters_characterSumData_PB_chC_apply__06e97235fe62
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
theorem _root_.solution : (chC : AddChar (E0 × H) ℂ) ≠ 0 := by
  intro h
  have h1 : (chC : AddChar (E0 × H) ℂ) (((1, 0), 0) : E0 × H)
      = (0 : AddChar (E0 × H) ℂ) (((1, 0), 0) : E0 × H) := by rw [h]
  have h2 : ¬ ((((1, 0), 0) : E0 × H).1.1 = 0) := by
    show ¬ ((1 : ZMod 2) = 0)
    decide
  rw [chC_apply', if_neg h2, zero_apply_lemma] at h1
  norm_num at h1
end Formalism.LFunctionChainParameters.characterSumData.PB
