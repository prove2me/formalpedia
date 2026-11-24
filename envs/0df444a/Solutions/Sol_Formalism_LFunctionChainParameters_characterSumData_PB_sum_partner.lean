-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.characterSumData.PB.sum_partner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:00:09.255649+00:00
-- url     : https://prove2.me/submissions/efe10d00-2fe7-4004-8662-82f1eec70bc4

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
open Formalism.LFunctionChainParameters.characterSumData.PB
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace Formalism.LFunctionChainParameters.characterSumData.PB
theorem _root_.solution {β : Type*} [AddCommMonoid β] (t : H) (F : E0 × H → β) :
    ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g), F (partner t g) = ∑ ρ ∈ PhiSet (H := H), F ρ := by
  refine Finset.sum_nbij' (partner t) (fun ρ => ρ - topPl t - cconj) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    simp only [PhiSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [inPhi_iff, partner_fst_lemma, (not_inPhi_iff a).1 ha]
    decide
  · intro a ha
    simp only [PhiSet, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [not_inPhi_iff, sub_fst_lemma_2, (inPhi_iff a).1 ha]
    decide
  · intro a _
    simp only [partner]
    abel
  · intro a _
    simp only [partner]
    abel
  · intro a _
    rfl
end Formalism.LFunctionChainParameters.characterSumData.PB
