-- Prove2me | solution 1 for FairChores.NineteenEighteenths.MMS_agent_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:29:52.76658+00:00
-- url     : https://prove2.me/submissions/c93c2331-aeea-4650-b2bb-5677719698b5

import Mathlib
import Definitions.Def_RequestProject_ChoresExamples
import Definitions.Def_RequestProject_ChoresMMSPartition
import Definitions.Def_RequestProject_FeigeNorkinChores
import Definitions.Def_RequestProject_NineteenEighteenths
import Theorems.Thm_FairChores_NineteenEighteenths_cast_sum_eq
import Theorems.Thm_FairChores_NineteenEighteenths_instC_nonneg
import Theorems.Thm_FairChores_NineteenEighteenths_R_le_instP
import Theorems.Thm_FairChores_FeigeNorkinChores_fcR_total
import Theorems.Thm_FairChores_MMS_le_of_outcome
import Theorems.Thm_FairChores_cbarSum_empty
import Theorems.Thm_FairChores_cbarSum_univ_le_nsmul_MMS
attribute [local simp] FairChores.cbarSum_empty



set_option autoImplicit true
open scoped BigOperators
open FairChores
open FairChores.NineteenEighteenths
open FeigeNorkinChores
namespace FairChores.NineteenEighteenths
theorem _root_.solution {lam : ℝ} (hlam : 2 ≤ lam) :
    MMS 3 (instC lam 0) (instP lam) = 360 := by
  have hlam0 : (0:ℝ) ≤ lam := by linarith
  have hc : ∀ t, 0 ≤ instC lam 0 t := fun t => instC_nonneg hlam0 0 t
  have hcbar : ∀ t, cbar (instC lam 0) (instP lam) t = (fcR t : ℝ) := by
    intro t
    have := R_le_instP hlam t
    simp only [cbar, instC, Matrix.cons_val_zero]
    exact min_eq_left this
  refine le_antisymm ?_ ?_
  · -- the explicit partition into three bundles of cost `360`
    refine MMS_le_of_outcome (n := 3) hc (by norm_num)
      (o := ⟨∅, ![{2, 3, 4}, {0, 1}, {5, 6, 7}], fun _ => 0⟩) ?_ ?_
    · refine ⟨fun _ => by simp, ?_, ?_, fun _ => le_rfl, by simp⟩
      · intro j k hjk
        have hj : j = 0 ∨ j = 1 ∨ j = 2 := by fin_cases j <;> simp
        have hk : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
        rcases hj with rfl | rfl | rfl <;> rcases hk with rfl | rfl | rfl <;>
          first
            | (exact absurd rfl hjk)
            | (simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
                Matrix.cons_val_two, Matrix.tail_cons]; decide)
      · simp only [Finset.empty_union]
        decide
    · intro j
      have hj : j = 0 ∨ j = 1 ∨ j = 2 := by fin_cases j <;> simp
      rcases hj with rfl | rfl | rfl <;>
        · simp only [cost, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
            Matrix.cons_val_two, Matrix.tail_cons, add_zero, instC]
          rw [cast_sum_eq _ fcR 360 (by decide)]
          norm_num
  · -- the total effective cost is `1080`
    have hbound := cbarSum_univ_le_nsmul_MMS (c := instC lam 0) (p := instP lam) (n := 3)
      hc (by norm_num)
    have hsum : cbarSum (instC lam 0) (instP lam) Finset.univ = 1080 := by
      simp only [cbarSum]
      rw [Finset.sum_congr rfl (fun t _ => hcbar t)]
      exact cast_sum_eq _ fcR 1080 fcR_total
    rw [hsum] at hbound
    norm_num at hbound
    linarith
end FairChores.NineteenEighteenths
