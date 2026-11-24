-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.characterSumData.double_coset_singleton
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:05:26.435715+00:00
-- url     : https://prove2.me/submissions/3778c3d3-d980-4d1f-ba4e-ff7e8480583e

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
end
end PB
open PB
section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
private theorem sgc0_fst_lemma_3 (x : E0 × H) : (x + sgc0).1.1 = x.1.1 + 1 := by
  simp [sgc0]
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
theorem _root_.solution : DCosetSingle (H := H) := by
  intro D hD i
  by_cases hf : InPhi (i • D.frob D.d)
  · refine ⟨i • D.frob D.d + sgc0, ⟨?_, ?_⟩, ?_⟩
    · rw [hD.inertia_d]
      right
      abel
    · rw [not_inPhi_iff, sgc0_fst_lemma_3, (inPhi_iff _).1 hf]
      decide
    · rintro y ⟨hy1, hy2⟩
      rcases (hD.inertia_d _).1 hy1 with h | h
      · exact absurd (by rw [sub_eq_zero.1 h]; exact hf) hy2
      · rw [sub_eq_iff_eq_add] at h
        rw [h, add_comm]
  · refine ⟨i • D.frob D.d, ⟨?_, hf⟩, ?_⟩
    · rw [hD.inertia_d]
      left
      exact sub_self _
    · rintro y ⟨hy1, hy2⟩
      rcases (hD.inertia_d _).1 hy1 with h | h
      · exact sub_eq_zero.1 h
      · exfalso
        apply hy2
        rw [sub_eq_iff_eq_add] at h
        rw [h, inPhi_iff, add_comm, sgc0_fst_lemma_3, (not_inPhi_iff _).1 hf]
        decide
end Formalism.LFunctionChainParameters.characterSumData
