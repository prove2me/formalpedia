-- Prove2me | solution 2 for Freiman.lower_h5_active_anchor
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-13T19:18:57.622969+00:00
-- url     : https://prove2.me/submissions/89d893b4-b2d5-42e7-87dc-60634f8993c5

import Definitions.Def_Freiman_lowerH5Data
import Theorems.Thm_Freiman_lowerHistory_theta_values
import Theorems.Thm_Freiman_lowerHistory_cf_value
import Mathlib.Tactic
import Theorems.Thm_Freiman_lower_h5_right3_anchor
import Theorems.Thm_Freiman_lower_h5_predecessor_coverage
import Theorems.Thm_Freiman_lower_h5_catalog
import Theorems.Thm_Freiman_lower_guard_offered
import Theorems.Thm_Freiman_lower_h5_initial_exclusion
import Theorems.Thm_Freiman_lower_h5_bindings
import Theorems.Thm_Freiman_lower_h5_reached_premises
import Theorems.Thm_Freiman_lowerHistory_goodness_semantics
import Theorems.Thm_Freiman_lowerHistory_pull_value
import Theorems.Thm_Freiman_lowerHistory_width_threshold
import Theorems.Thm_Freiman_lower_h5_numeric_to_anchor
import Theorems.Thm_Freiman_lowerHistory_endpoint_semantics
import Theorems.Thm_Freiman_lowerHistory_greater_semantics
import Theorems.Thm_Freiman_lower_h5_numerics
import Theorems.Thm_Freiman_lower_h5_exception_anchor
import Definitions.Def_Freiman_lowerH5Verification
import Definitions.Def_Freiman_lowerInitialEntry

open Freiman

attribute [local instance] Classical.propDecidable

private theorem exceptional_right (c : LowerH5Case)
    (hm : c ∈ lowerH5Cases) (he : lowerH5Exceptional c) :
    c.context.words.2 = [3,1] := by
  simp only [lowerH5Cases, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h <;> subst c <;>
    simp_all [lowerH5Exceptional]

private theorem threshold_value (c : CertField) (x y : CertField × CertField)
    (r s : ℝ) :
    certThresholdVal (lowerHistoryThreshold c x y) r s =
      certFieldVal c * ((1+s*certFieldVal y.1)*(1+s*certFieldVal y.2)) /
        ((1+r*certFieldVal x.1)*(1+r*certFieldVal x.2)) := by
  simp only [lowerHistoryThreshold, lowerHistorySort]
  split <;> split <;>
    simp only [certThresholdVal, certThresholdNum, certThresholdDen] <;> ring

private theorem tau_nonnegative : 0 ≤ certFieldVal lowerHistoryTau := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hn := Real.sqrt_nonneg (3 : ℝ)
  norm_num [lowerHistoryTau, certFieldVal]

private theorem cf213_value :
    certFieldVal (lowerHistoryCF [2,1,3] lowerHistoryTau) = lowerTheta 30 := by
  rw [Freiman.lowerHistory_cf_value _ _ tau_nonnegative]
  norm_num [certFieldVal, lowerHistoryTau, lowerTau, lowerTheta]
  congr 1 <;> ring

private theorem h7_value (p : LowerPair) :
    certThresholdVal lowerHistoryH7.threshold
      (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2) =
      lowerThreshold p (31/100) 3 63 25 66 := by
  simp only [lowerHistoryH7, lowerHistoryPB, threshold_value, lowerThreshold,
    lowerHistory_theta_values 3 (by simp),
    lowerHistory_theta_values 25 (by simp),
    lowerHistory_theta_values 63 (by simp),
    lowerHistory_theta_values 66 (by simp)]
  norm_num [lowerHistoryRat, certFieldVal]

private theorem h9_value (p : LowerPair) :
    certThresholdVal lowerHistoryH9.threshold
      (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2) =
      lowerThreshold p ((3-Real.sqrt 3)/2) 36 63 63 66 := by
  simp only [lowerHistoryH9, lowerHistoryPB, threshold_value, lowerThreshold,
    lowerHistory_theta_values 36 (by simp),
    lowerHistory_theta_values 63 (by simp),
    lowerHistory_theta_values 66 (by simp)]
  norm_num [certFieldVal]
  ring

private theorem h18_value (p : LowerPair) :
    certThresholdVal lowerH5H18.threshold
      (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2) =
      lowerThreshold p (183/250) 25 36 30 63 := by
  simp only [lowerH5H18, threshold_value, lowerThreshold,
    lowerHistory_theta_values 25 (by simp),
    lowerHistory_theta_values 36 (by simp),
    lowerHistory_theta_values 63 (by simp), cf213_value]
  norm_num [lowerHistoryRat, certFieldVal]

private theorem exceptional_cut_semantics (p : LowerPair)
    (hc : lowerHistoryAtBase (lowerNormalize p)
      [lowerHistoryH7, lowerHistoryH9, lowerH5H18]) :
    ¬ lowerA p 3 ∧ lowerA p 9 ∧ ¬ lowerA p 16 := by
  have h7 := hc lowerHistoryH7 (by simp)
  have h9 := hc lowerHistoryH9 (by simp)
  have h18 := hc lowerH5H18 (by simp)
  change certThresholdVal lowerHistoryH7.threshold
    (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2) ≤
      lowerScale (lowerNormalize p) at h7
  change lowerScale (lowerNormalize p) ≤ certThresholdVal lowerHistoryH9.threshold
    (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2) at h9
  change lowerScale (lowerNormalize p) ≤ certThresholdVal lowerH5H18.threshold
    (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2) at h18
  rw [h7_value p] at h7
  rw [h9_value p] at h9
  rw [h18_value p] at h18
  change ¬ lowerScale (lowerNormalize p) < _ ∧
    lowerScale (lowerNormalize p) ≤ _ ∧
    ¬ lowerScale (lowerNormalize p) > _
  exact ⟨not_lt_of_ge h7, h9, not_lt_of_ge h18⟩

private theorem exceptional_cuts (base : LowerPair) (c : LowerH5Case)
    (hs : lowerH5CaseShape c) (he : lowerH5Exceptional c)
    (hc : lowerHistoryAtBase base c.oldCuts) :
    lowerHistoryAtBase base [lowerHistoryH7, lowerHistoryH9, lowerH5H18] := by
  intro b hb
  apply hc b
  have hfin : c.oldCuts.toFinset =
      ([lowerHistoryH7, lowerHistoryH9, lowerH5H18] : List CertBound).toFinset := by
    rw [hs.2.2.2.1, he.1]
    rfl
  apply List.mem_toFinset.mp
  rw [hfin]
  exact List.mem_toFinset.mpr hb

private theorem exceptional_left_not (c : LowerH5Case) (he : lowerH5Exceptional c) :
    ¬ lowerEnds c.context.words.1 [3,1] := by
  have hm : c.context.words.1 = [1] ∨ c.context.words.1 = [2] ∨
      c.context.words.1 = [3] := by simpa using he.2
  rcases hm with h | h | h
  · rw [h]
    intro hs
    have := hs.length_le
    norm_num at this
  · rw [h]
    intro hs
    have := hs.length_le
    norm_num at this
  · rw [h]
    intro hs
    have := hs.length_le
    norm_num at this

private theorem parity_equal_of_exceptional (base : LowerPair) (c : LowerH5Case)
    (hs : lowerH5CaseShape c) (he : lowerH5Exceptional c)
    (hf : lowerHistoryContextFits base c.context) :
    base.1.length % 2 = base.2.length % 2 := by
  have hp : c.context.parity = (false,false) := by
    rw [hs.2.1, he.1]
    rfl
  have hdec := hf.2.2
  rw [hp] at hdec
  simp only [Bool.xor_false] at hdec
  by_cases h₁ : base.1.length % 2 = 1
  · have h₂ : base.2.length % 2 = 1 := by simpa [h₁] using hdec
    omega
  · have h₂ : base.2.length % 2 ≠ 1 := by
      intro hh
      simp [h₁, hh] at hdec
    omega

private theorem lowerChild_injective (p : LowerPair) : Function.Injective (lowerChild p) := by
  rintro ⟨a,b⟩ ⟨c,d⟩ h
  simp only [lowerChild] at h
  injection h with h₁ h₂
  have h₁' : a.reverse = c.reverse := (List.append_right_injective _ h₁)
  have h₂' : b = d := (List.append_right_injective _ h₂)
  have h₁'' : a = c := by
    simpa using congrArg List.reverse h₁'
  exact Prod.ext h₁'' h₂'

private theorem lower_h5_exception_event_mem (t : ℝ) (h : ℕ → LowerPair) (n : ℕ)
    (hh : lowerHistory t h n) (c : LowerH5Case)
    (hmem : c ∈ lowerH5Cases) (hshape : lowerH5CaseShape c)
    (hc : lowerH5Immediate h n c) (he : lowerH5Exceptional c) :
    ∃ m : ℕ, LowerH5PriorityEvent t h n m := by
  rcases hc with ⟨m, hmn, hfit, hphysical, _hnormal, hcuts⟩
  let base := lowerNormalize (h m)
  have hwords : c.words = ([2],[]) := by
    rw [hshape.1, he.1]
    rfl
  have hselected : h n = lowerChild (h m) ([2],[]) := by
    rw [hwords] at hphysical
    simpa [base, lowerHistoryAppend, lowerChild] using hphysical
  have hearlier : m < n := by omega
  have hcut := exceptional_cuts base c hshape he hcuts
  have hA := exceptional_cut_semantics (h m) (by simpa [base] using hcut)
  have hpar := parity_equal_of_exceptional base c hshape he hfit
  have hnotmixed : ¬ lowerMixed (h m) := by
    dsimp [base] at hpar
    unfold lowerMixed
    unfold lowerNormalize at hpar
    split at hpar <;> simp_all only [Prod.fst, Prod.snd] <;> omega
  have hnotL : ¬ lowerL (h m) := by
    change ¬ lowerEnds base.1 [3,1]
    intro hl
    exact exceptional_left_not c he (hfit.1.2.2.mp hl)
  have hR : lowerR (h m) := by
    change lowerEnds base.2 [3,1]
    apply hfit.2.1.2.2.mpr
    rw [exceptional_right c hmem he]
    simp [lowerEnds]
  obtain ⟨l, _hoff, hpriority, hstep⟩ := hh.2.2 m hearlier
  have hl : l = ([2],[]) := by
    apply lowerChild_injective (h m)
    rw [← hstep, hmn, hselected]
  subst l
  exact ⟨m, ⟨hearlier, hmn,
    ⟨hnotmixed, hA.1, hA.2.1, hnotL, hR, hA.2.2⟩,
    hselected, hpriority⟩⟩

theorem solution (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n)
    (ha : lowerH5Active (h n)) : lowerH5LowerBound (h n) t := by
  by_cases hr : lowerEnds (lowerNormalize (h n)).2 [3]
  · exact lower_h5_right3_anchor (h n) t (hh.2.1 n (Nat.le_refl n)) ha hr
  · obtain ⟨c,hc,him⟩ := lower_h5_predecessor_coverage lower_h5_catalog lower_guard_offered lower_h5_initial_exclusion t h n hh ha hr
    have hshape := (lower_h5_bindings c hc).1
    have hsrc := lower_h5_reached_premises lowerHistory_goodness_semantics lowerHistory_pull_value lowerHistory_width_threshold t h n hh ha c hshape him
    rcases lower_h5_numeric_to_anchor lowerHistory_endpoint_semantics lowerHistory_greater_semantics t h n hh ha c hshape him hsrc (lower_h5_numerics c hc) with hb | he
    · exact hb
    · obtain ⟨m,hm⟩ := lower_h5_exception_event_mem t h n hh c hc hshape him he
      exact lower_h5_exception_anchor t h n m hh hm

#print axioms lower_h5_exception_event_mem
#print axioms solution
