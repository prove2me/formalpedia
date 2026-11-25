-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.characterSumData.partner_bijection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:15:05.265903+00:00
-- url     : https://prove2.me/submissions/fb1d12c8-2543-4f90-8d8d-0d59cccbd4e2

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
private theorem sub_fst_lemma_2 (t : H) (ρ : E0 × H) : (ρ - topPl t - cconj).1.1 = ρ.1.1 - 1 := by
  simp [topPl, cconj]
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
theorem _root_.solution : PartnerBij (H := H) := by
  intro t
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    show InPhi (partner t g)
    rw [inPhi_iff, partner_fst_lemma, (not_inPhi_iff g).1 hg]
    decide
  · intro x _ y _ hxy
    simp only [partner] at hxy
    exact add_left_cancel (add_right_cancel hxy)
  · intro ρ hρ
    refine ⟨ρ - topPl t - cconj, ?_, ?_⟩
    · show ¬ InPhi (ρ - topPl t - cconj)
      rw [not_inPhi_iff, sub_fst_lemma_2, (inPhi_iff ρ).1 hρ]
      decide
    · simp only [partner]
      abel
end Formalism.LFunctionChainParameters.characterSumData
