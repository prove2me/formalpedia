-- Prove2me | solution 1 for FirstPassageLinearTransport.exists_collatzThreeBlockEnvelopeMass_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:59:12.528302+00:00
-- url     : https://prove2.me/submissions/7f70c8ec-59a2-4c9f-b69f-febfe898c24f

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_lowerSurvivalMass_mem_unit
import Theorems.Thm_FirstPassageLinearTransport_collatzTilt_pos
import Theorems.Thm_FirstPassageLinearTransport_collatzTilt_lt_one
import Theorems.Thm_FirstPassageLinearTransport_collatzTiltVariance_pos
import Theorems.Thm_FirstPassageLinearTransport_collatzLowerSurvivalMass_le
import Theorems.Thm_FirstPassageLinearTransport_collatzNegLowerSurvivalMass_le
import Theorems.Thm_FirstPassageLinearTransport_weightedSurvivalWordMass_eq_lowerSurvivalMass
import Theorems.Thm_FirstPassageLinearTransport_exists_collatzMiddleIntervalMass_uniform_le_sqrt
import Theorems.Thm_FirstPassageLinearTransport_weightedSurvivalFactor_nonneg
import Theorems.Thm_FirstPassageLinearTransport_sum_weightedSurvivalFactor_eq
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ a b : ℕ, ∀ B q center : ℝ,
        0 < a → 0 < b → 0 ≤ B → 0 ≤ q →
          collatzThreeBlockEnvelopeMass a b B q center ≤
            C * (B + 1) * (q + 2) /
              (Real.sqrt a * Real.sqrt a * Real.sqrt b) := by
  obtain ⟨Cmid, hCmid, hmid⟩ :=
    exists_collatzMiddleIntervalMass_uniform_le_sqrt
  let Csurv : ℝ := 1 + 2 / collatzTiltVariance
  have hCsurv : 0 < Csurv := by
    dsimp [Csurv]
    have hdiv : 0 < (2 : ℝ) / collatzTiltVariance :=
      div_pos (by norm_num) collatzTiltVariance_pos
    linarith
  refine ⟨Csurv ^ 2 * Cmid, mul_pos (sq_pos_of_pos hCsurv) hCmid, ?_⟩
  intro a b B q center ha hb hB hq
  have hsFirst :
      weightedSurvivalWordMass collatzTilt collatzLogIncrement (-B) a 0 ≤
        Csurv * (B + 1) / Real.sqrt a := by
    rw [weightedSurvivalWordMass_eq_lowerSurvivalMass]
    simpa [Csurv] using collatzLowerSurvivalMass_le hB ha
  have hsLast :
      weightedSurvivalWordMass collatzTilt
          (fun bit ↦ -collatzLogIncrement bit) (-(q + 1)) a 0 ≤
        Csurv * (q + 2) / Real.sqrt a := by
    rw [weightedSurvivalWordMass_eq_lowerSurvivalMass]
    dsimp [Csurv]
    convert collatzNegLowerSurvivalMass_le
      (B := q + 1) (by linarith) ha using 1
    all_goals ring
  have hfirstNonneg :
      0 ≤ weightedSurvivalWordMass collatzTilt collatzLogIncrement (-B) a 0 := by
    rw [weightedSurvivalWordMass_eq_lowerSurvivalMass]
    exact (lowerSurvivalMass_mem_unit collatzTilt_pos.le collatzTilt_lt_one.le
      collatzLogIncrement (-B) a 0).1
  have hlastNonneg :
      0 ≤ weightedSurvivalWordMass collatzTilt
        (fun bit ↦ -collatzLogIncrement bit) (-(q + 1)) a 0 := by
    rw [weightedSurvivalWordMass_eq_lowerSurvivalMass]
    exact (lowerSurvivalMass_mem_unit collatzTilt_pos.le collatzTilt_lt_one.le
      (fun bit ↦ -collatzLogIncrement bit) (-(q + 1)) a 0).1
  have hinner : ∀ u : Fin a → Bool,
      (∑ w : Fin a → Bool,
        weightedSurvivalFactor collatzTilt
            (fun bit ↦ -collatzLogIncrement bit) (-(q + 1)) 0 w *
          collatzMiddleIntervalMass b
            (center - wordIncrementSum collatzLogIncrement u +
              wordIncrementSum (fun bit ↦ -collatzLogIncrement bit) w)) ≤
        weightedSurvivalWordMass collatzTilt
            (fun bit ↦ -collatzLogIncrement bit) (-(q + 1)) a 0 *
          (Cmid / Real.sqrt b) := by
    intro u
    calc
      (∑ w : Fin a → Bool,
        weightedSurvivalFactor collatzTilt
            (fun bit ↦ -collatzLogIncrement bit) (-(q + 1)) 0 w *
          collatzMiddleIntervalMass b
            (center - wordIncrementSum collatzLogIncrement u +
              wordIncrementSum (fun bit ↦ -collatzLogIncrement bit) w)) ≤
          ∑ w : Fin a → Bool,
            weightedSurvivalFactor collatzTilt
                (fun bit ↦ -collatzLogIncrement bit) (-(q + 1)) 0 w *
              (Cmid / Real.sqrt b) := by
            apply Finset.sum_le_sum
            intro w _hw
            exact mul_le_mul_of_nonneg_left (hmid b _ hb)
              (weightedSurvivalFactor_nonneg
                collatzTilt_pos.le collatzTilt_lt_one.le _ _ _ w)
      _ = weightedSurvivalWordMass collatzTilt
            (fun bit ↦ -collatzLogIncrement bit) (-(q + 1)) a 0 *
          (Cmid / Real.sqrt b) := by
            rw [← Finset.sum_mul, sum_weightedSurvivalFactor_eq]
  have hmass :
      collatzThreeBlockEnvelopeMass a b B q center ≤
        weightedSurvivalWordMass collatzTilt collatzLogIncrement (-B) a 0 *
          (weightedSurvivalWordMass collatzTilt
              (fun bit ↦ -collatzLogIncrement bit) (-(q + 1)) a 0 *
            (Cmid / Real.sqrt b)) := by
    unfold collatzThreeBlockEnvelopeMass
    calc
      _ ≤ ∑ u : Fin a → Bool,
          weightedSurvivalFactor collatzTilt collatzLogIncrement (-B) 0 u *
            (weightedSurvivalWordMass collatzTilt
                (fun bit ↦ -collatzLogIncrement bit) (-(q + 1)) a 0 *
              (Cmid / Real.sqrt b)) := by
            apply Finset.sum_le_sum
            intro u _hu
            exact mul_le_mul_of_nonneg_left (hinner u)
              (weightedSurvivalFactor_nonneg
                collatzTilt_pos.le collatzTilt_lt_one.le _ _ _ u)
      _ = _ := by
        rw [← Finset.sum_mul, sum_weightedSurvivalFactor_eq]
  have hCmidNonneg : 0 ≤ Cmid / Real.sqrt b :=
    div_nonneg hCmid.le (Real.sqrt_nonneg _)
  calc
    collatzThreeBlockEnvelopeMass a b B q center ≤
        weightedSurvivalWordMass collatzTilt collatzLogIncrement (-B) a 0 *
          (weightedSurvivalWordMass collatzTilt
              (fun bit ↦ -collatzLogIncrement bit) (-(q + 1)) a 0 *
            (Cmid / Real.sqrt b)) := hmass
    _ ≤ (Csurv * (B + 1) / Real.sqrt a) *
          ((Csurv * (q + 2) / Real.sqrt a) * (Cmid / Real.sqrt b)) := by
      gcongr
    _ = (Csurv ^ 2 * Cmid) * (B + 1) * (q + 2) /
          (Real.sqrt a * Real.sqrt a * Real.sqrt b) := by ring
end FirstPassageLinearTransport
