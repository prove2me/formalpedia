-- Prove2me | solution 1 for FairSelling.ElevenTwelfths.MMS_agent_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:19:32.757825+00:00
-- url     : https://prove2.me/submissions/f1f84a1e-ae21-42e6-806d-4999ef421699

import Mathlib
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_FeigeNorkin
import Definitions.Def_RequestProject_ElevenTwelfths
import Theorems.Thm_FairSelling_ElevenTwelfths_cast_sum_eq
import Theorems.Thm_FairSelling_ElevenTwelfths_instV_nonneg
import Theorems.Thm_FairSelling_ElevenTwelfths_instP_nonneg
import Theorems.Thm_FairSelling_ElevenTwelfths_instP_le_R
import Theorems.Thm_FairSelling_FeigeNorkin_fnR_total
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
    MMS 3 (instV 0) (instP δ) = 36 := by
  refine le_antisymm ?_ ?_
  · -- `MMS ≤ TPS ≤ PS = 36`
    have h := MMS_le_TPS_le_PS (instV 0) (instP δ) (n := 3) (by norm_num)
      (fun g => instV_nonneg 0 g) (instP_nonneg hδ0)
    have hPS : PS 3 (instV 0) (instP δ) = 36 := by
      unfold PS
      have : (∑ g, max (instP δ g) (instV 0 g)) = ∑ g, (fnR g : ℝ) := by
        refine Finset.sum_congr rfl (fun g _ => ?_)
        rw [max_eq_right (instP_le_R hδ g)]
        rfl
      rw [this, cast_sum_eq Finset.univ fnR 108 fnR_total]
      norm_num
    linarith [h.1, h.2]
  · -- the explicit partition into three bundles of value `36`
    refine le_MMS_of_outcome (by norm_num) (instV 0) (instP δ)
      (fun g => instV_nonneg 0 g) (instP_nonneg hδ0)
      ⟨∅, ![{2, 3, 4}, {0, 1}, {5, 6, 7}], fun _ => 0⟩ ?_ 36 ?_
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
          show (36 : ℝ) ≤ ∑ g ∈ _, (fnR g : ℝ)
          rw [cast_sum_eq _ fnR 36 (by decide)]
          norm_num
end FairSelling.ElevenTwelfths
