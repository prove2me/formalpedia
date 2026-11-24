-- Prove2me | solution 1 for FairChores.NineteenEighteenths.MMS_agent_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:30:28.66006+00:00
-- url     : https://prove2.me/submissions/2e1769fd-15d1-4d10-8e94-08ed5e52c165

import Mathlib
import Definitions.Def_RequestProject_ChoresExamples
import Definitions.Def_RequestProject_ChoresMMSPartition
import Definitions.Def_RequestProject_FeigeNorkinChores
import Definitions.Def_RequestProject_NineteenEighteenths
import Theorems.Thm_FairChores_NineteenEighteenths_instC_nonneg
import Theorems.Thm_FairChores_NineteenEighteenths_instP_sum
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
theorem _root_.solution {lam : ℝ} (hlam0 : 0 ≤ lam) :
    MMS 3 (instC lam 2) (instP lam) = 360 * lam := by
  have hc : ∀ t, 0 ≤ instC lam 2 t := fun t => instC_nonneg hlam0 2 t
  have hcbar : ∀ t, cbar (instC lam 2) (instP lam) t = instP lam t := by
    intro t
    simp only [cbar, instC, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, min_self]
  refine le_antisymm ?_ ?_
  · -- outsource everything and split the bill in three
    refine MMS_le_of_outcome (n := 3) hc (by norm_num)
      (o := ⟨Finset.univ, fun _ => ∅, fun _ => 360 * lam⟩) ?_ ?_
    · refine ⟨fun _ => by simp, fun _ _ _ => by simp, by simp, fun _ => by positivity, ?_⟩
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [instP_sum]
      push_cast
      linarith
    · intro j
      simp only [cost, Finset.sum_empty, zero_add]
      exact le_rfl
  · have hbound := cbarSum_univ_le_nsmul_MMS (c := instC lam 2) (p := instP lam) (n := 3)
      hc (by norm_num)
    have hsum : cbarSum (instC lam 2) (instP lam) Finset.univ = 1080 * lam := by
      simp only [cbarSum]
      rw [Finset.sum_congr rfl (fun t _ => hcbar t)]
      exact instP_sum lam
    rw [hsum] at hbound
    norm_num at hbound
    linarith
end FairChores.NineteenEighteenths
