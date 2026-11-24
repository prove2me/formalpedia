-- Prove2me | solution 1 for FairSelling.ElevenTwelfths.MMS_agent_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:19:44.835799+00:00
-- url     : https://prove2.me/submissions/5f62d876-5601-4120-86a6-dfaa8ef9b9cb

import Mathlib
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_FeigeNorkin
import Definitions.Def_RequestProject_ElevenTwelfths
import Theorems.Thm_FairSelling_ElevenTwelfths_cast_sum_eq
import Theorems.Thm_FairSelling_ElevenTwelfths_instV_nonneg
import Theorems.Thm_FairSelling_ElevenTwelfths_instP_nonneg
import Theorems.Thm_FairSelling_ElevenTwelfths_instP_le_C
import Theorems.Thm_FairSelling_FeigeNorkin_fnC_total
import Theorems.Thm_FairSelling_MMS_le_TPS_le_PS
import Theorems.Thm_FairSelling_le_MMS_of_outcome
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.ElevenTwelfths
open FeigeNorkin
namespace FairSelling.ElevenTwelfths
theorem _root_.solution {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1/12) :
    MMS 3 (instV 1) (instP δ) = 36 := by
  refine le_antisymm ?_ ?_
  · have h := MMS_le_TPS_le_PS (instV 1) (instP δ) (n := 3) (by norm_num)
      (fun g => instV_nonneg 1 g) (instP_nonneg hδ0)
    have hPS : PS 3 (instV 1) (instP δ) = 36 := by
      unfold PS
      have : (∑ g, max (instP δ g) (instV 1 g)) = ∑ g, (fnC g : ℝ) := by
        refine Finset.sum_congr rfl (fun g _ => ?_)
        rw [max_eq_right (instP_le_C hδ g)]
        rfl
      rw [this, cast_sum_eq Finset.univ fnC 108 fnC_total]
      norm_num
    linarith [h.1, h.2]
  · refine le_MMS_of_outcome (by norm_num) (instV 1) (instP δ)
      (fun g => instV_nonneg 1 g) (instP_nonneg hδ0)
      ⟨∅, ![{2, 5}, {0, 3, 6}, {1, 4, 7}], fun _ => 0⟩ ?_ 36 ?_
    · refine ⟨fun _ => by simp, ?_, fun _ => le_refl 0, by simp⟩
      intro j k hjk
      have hj : j = 0 ∨ j = 1 ∨ j = 2 := by fin_cases j <;> simp
      have hk : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
      rcases hj with rfl | rfl | rfl <;> rcases hk with rfl | rfl | rfl <;>
        first
          | (exact absurd rfl hjk)
          | (simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
              Matrix.cons_val_two, Matrix.tail_cons]; decide)
    · intro j
      have hj : j = 0 ∨ j = 1 ∨ j = 2 := by fin_cases j <;> simp
      rcases hj with rfl | rfl | rfl <;>
        · simp only [util, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
            Matrix.cons_val_two, Matrix.tail_cons, add_zero]
          show (36 : ℝ) ≤ ∑ g ∈ _, (fnC g : ℝ)
          rw [cast_sum_eq _ fnC 36 (by decide)]
          norm_num
end FairSelling.ElevenTwelfths
