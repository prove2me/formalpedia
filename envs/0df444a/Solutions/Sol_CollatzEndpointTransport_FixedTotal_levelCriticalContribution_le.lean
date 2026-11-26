-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.levelCriticalContribution_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:41:28.9528+00:00
-- url     : https://prove2.me/submissions/25e12506-f9d0-4c73-8804-96f05202c530

import Definitions.Def_CollatzEndpointTransport_Linear_FiniteFiberMixture
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalGlobalEndpointMoment
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_levelCriticalNumerator_le
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedCriticalNumerator_div_level_le
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_cohortCriticalNumerator_le
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumerator_prependOne
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_wordCorrectionFrom_nil
import Theorems.Thm_CollatzEndpointTransport_Terras_integerCorrection_zero
attribute [local simp] CollatzEndpointTransport.FixedTotal.encodeBlocks_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.encodeBlocks_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumerator_prependOne
attribute [local simp] CollatzEndpointTransport.FixedTotal.wordCorrectionFrom_nil
attribute [local simp] CollatzEndpointTransport.Terras.integerCorrection_zero



set_option autoImplicit false
set_option maxHeartbeats 2000000
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.globalCompositionDecidableEq
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    (M s : ℕ) :
    levelCriticalContribution M s ≤
      Real.sqrt M *
        ∑ u : Fin M,
          fixedCriticalContribution (M - (u : ℕ)) s := by
  by_cases hlevel : levelSourceCard M s = 0
  · have hall :
        ∀ u : Fin M, (levelCohortSet M s u).card = 0 := by
      intro u
      have hle :
          (levelCohortSet M s u).card ≤ levelSourceCard M s :=
        Finset.single_le_sum
          (fun i _ => Nat.zero_le (levelCohortSet M s i).card)
          (Finset.mem_univ u)
      omega
    have htarget : levelEndpointSet M s = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro y hy
      rcases Finset.mem_biUnion.mp hy with ⟨u, hu, hyu⟩
      have hset :
          levelCohortSet M s u = ∅ :=
        Finset.card_eq_zero.mp (hall u)
      simp [hset] at hyu
    simp [levelCriticalContribution, levelCriticalNumerator,
      levelEndpointSet, htarget, hlevel]
    unfold fixedCriticalContribution fixedCriticalNumerator
    positivity
  · have hlevelPos : 0 < levelSourceCard M s :=
      Nat.pos_of_ne_zero hlevel
    have hsqrtLevel :
        0 < Real.sqrt (levelSourceCard M s) := by
      exact Real.sqrt_pos.mpr (by exact_mod_cast hlevelPos)
    calc
      levelCriticalContribution M s =
          levelCriticalNumerator M s /
            Real.sqrt (levelSourceCard M s) := rfl
      _ ≤ (Real.sqrt M *
            ∑ u : Fin M, cohortCriticalNumerator M u s) /
            Real.sqrt (levelSourceCard M s) := by
        exact div_le_div_of_nonneg_right
          (levelCriticalNumerator_le M s)
          (Real.sqrt_nonneg _)
      _ ≤ (Real.sqrt M *
            ∑ u : Fin M,
              fixedCriticalNumerator (M - (u : ℕ)) s) /
            Real.sqrt (levelSourceCard M s) := by
        gcongr
        exact cohortCriticalNumerator_le M _ s
      _ = Real.sqrt M *
            ∑ u : Fin M,
              (fixedCriticalNumerator (M - (u : ℕ)) s /
                Real.sqrt (levelSourceCard M s)) := by
        simp only [div_eq_mul_inv]
        calc
          Real.sqrt M *
                (∑ u : Fin M,
                  fixedCriticalNumerator (M - (u : ℕ)) s) *
                (Real.sqrt (levelSourceCard M s))⁻¹ =
              (∑ u : Fin M,
                  Real.sqrt M *
                    fixedCriticalNumerator (M - (u : ℕ)) s) *
                (Real.sqrt (levelSourceCard M s))⁻¹ := by
            rw [Finset.mul_sum]
          _ = ∑ u : Fin M,
                (Real.sqrt M *
                  fixedCriticalNumerator (M - (u : ℕ)) s) *
                    (Real.sqrt (levelSourceCard M s))⁻¹ := by
            rw [Finset.sum_mul]
          _ = Real.sqrt M *
                ∑ u : Fin M,
                  fixedCriticalNumerator (M - (u : ℕ)) s *
                    (Real.sqrt (levelSourceCard M s))⁻¹ := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro u hu
            ring
      _ ≤ Real.sqrt M *
            ∑ u : Fin M,
              fixedCriticalContribution (M - (u : ℕ)) s := by
        gcongr
        exact fixedCriticalNumerator_div_level_le M s _ hlevelPos
end CollatzEndpointTransport.FixedTotal
