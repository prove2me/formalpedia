-- Prove2me | solution 1 for Formalism.ResultantValuation.LaplaceProof.image_glue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:36:44.131315+00:00
-- url     : https://prove2.me/submissions/50b9fd88-1ba7-46a0-bfd3-4de2e682c02d

import Definitions.Def_Formalism_ResultantValuation_ResultantConjugate
import Definitions.Def_Formalism_ResultantValuation_ResultantAdjugateProofs_Laplace
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_shuffle_castAdd
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_shuffle_natAdd
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_glue_castAdd
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_glue_natAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.ResultantValuation.LaplaceProof.shuffle_castAdd
attribute [local simp] Formalism.ResultantValuation.LaplaceProof.shuffle_natAdd
attribute [local simp] Formalism.ResultantValuation.LaplaceProof.glue_castAdd
attribute [local simp] Formalism.ResultantValuation.LaplaceProof.glue_natAdd

set_option autoImplicit false
open Finset Equiv
noncomputable section
open Formalism Formalism.ResultantValuation
open Formalism.ResultantValuation.LaplaceProof
variable {a b : ℕ}
namespace Formalism.ResultantValuation.LaplaceProof
theorem _root_.solution (x : Σ _ : {J : Finset (Fin (a + b)) // J.card = a},
    Perm (Fin a) × Perm (Fin b)) :
    univ.image (fun i => glue x (Fin.castAdd b i)) = x.1.1 := by
  simp only [glue_castAdd]
  ext y
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact Finset.orderEmbOfFin_mem _ _ _
  · intro hy
    have hr : y ∈ Set.range (x.1.1.orderEmbOfFin x.1.2) := by
      rw [Finset.range_orderEmbOfFin]
      exact Finset.mem_coe.mpr hy
    obtain ⟨k, rfl⟩ := hr
    exact ⟨x.2.1.symm k, by simp⟩
end Formalism.ResultantValuation.LaplaceProof
