-- Prove2me | solution 1 for Freiman.trunk_early_plan
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-13T15:53:00.154286+00:00
-- url     : https://prove2.me/submissions/ddeb7915-6757-468a-ba40-09e18130285c

import Definitions.Def_Freiman_trunkGeometry
import Theorems.Thm_Freiman_lowerHistory_theta_values
import Theorems.Thm_Freiman_lowerHistory_cf_value
import Mathlib.Tactic

set_option Elab.async false

open Freiman
attribute [local instance] Classical.propDecidable

private theorem threshold_value (c : CertField) (x y : CertField × CertField)
    (r s : ℝ) :
    certThresholdVal (lowerHistoryThreshold c x y) r s =
      certFieldVal c * ((1+s*certFieldVal y.1)*(1+s*certFieldVal y.2)) /
        ((1+r*certFieldVal x.1)*(1+r*certFieldVal x.2)) := by
  simp only [lowerHistoryThreshold,lowerHistorySort]
  split <;> split <;>
    simp only [certThresholdVal,certThresholdNum,certThresholdDen] <;> ring

private theorem h7_value (p : LowerPair) :
    certThresholdVal lowerHistoryH7.threshold
      (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2) =
      lowerThreshold p (31/100) 3 63 25 66 := by
  simp only [lowerHistoryH7,lowerHistoryPB,threshold_value,lowerThreshold,
    lowerHistory_theta_values 3 (by simp),lowerHistory_theta_values 25 (by simp),
    lowerHistory_theta_values 63 (by simp),lowerHistory_theta_values 66 (by simp)]
  norm_num [lowerHistoryRat,certFieldVal]

private theorem h9_value (p : LowerPair) :
    certThresholdVal lowerHistoryH9.threshold
      (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2) =
      lowerThreshold p ((3-Real.sqrt 3)/2) 36 63 63 66 := by
  simp only [lowerHistoryH9,lowerHistoryPB,threshold_value,lowerThreshold,
    lowerHistory_theta_values 36 (by simp),lowerHistory_theta_values 63 (by simp),
    lowerHistory_theta_values 66 (by simp)]
  norm_num [certFieldVal]
  ring

private theorem tau_nonnegative : 0 ≤ certFieldVal lowerHistoryTau := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hn := Real.sqrt_nonneg (3 : ℝ)
  norm_num [lowerHistoryTau,certFieldVal]

private theorem cf213_value :
    certFieldVal (lowerHistoryCF [2,1,3] lowerHistoryTau) = lowerTheta 30 := by
  rw [lowerHistory_cf_value _ _ tau_nonnegative]
  norm_num [certFieldVal,lowerHistoryTau,lowerTau,lowerTheta]
  congr 1 <;> ring

private theorem h18_value (p : LowerPair) :
    certThresholdVal trunkH18.threshold
      (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2) =
      lowerThreshold p (183/250) 25 36 30 63 := by
  simp only [trunkH18,threshold_value,lowerThreshold,
    lowerHistory_theta_values 25 (by simp),lowerHistory_theta_values 36 (by simp),
    lowerHistory_theta_values 63 (by simp),cf213_value]
  norm_num [lowerHistoryRat,certFieldVal]

private theorem small_marked_cuts (p : LowerPair) (h3 : ¬ lowerA p 3)
    (h9 : lowerA p 9) (h16 : ¬ lowerA p 16) :
    trunkHolds [lowerHistoryH7,lowerHistoryH9,trunkH18]
      (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2)
      (lowerScale (lowerNormalize p)) := by
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl
  · change certThresholdVal lowerHistoryH7.threshold _ _ ≤ lowerScale (lowerNormalize p)
    rw [h7_value]
    exact le_of_not_gt h3
  · change lowerScale (lowerNormalize p) ≤ certThresholdVal lowerHistoryH9.threshold _ _
    rw [h9_value]
    exact h9
  · change lowerScale (lowerNormalize p) ≤ certThresholdVal trunkH18.threshold _ _
    rw [h18_value]
    exact le_of_not_gt h16

theorem solution (t : ℝ) (p : LowerPair) (hs : lowerState t p)
    (hd : lowerEarlyDomain p) (k : Fin 16)
    (hf : lowerHistoryContextFits (lowerNormalize p) (trunkCatalog.states k).context) :
    ∃ pi : ℕ, pi < (trunkSourcePlans (trunkCatalog.states k).context).length ∧
    trunkHolds (trunkPlanAt (trunkCatalog.states k) pi).cuts
      (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2)
      (lowerScale (lowerNormalize p)) ∧
    ([3],[2]) ∈ (trunkPlanAt (trunkCatalog.states k) pi).labels ∧
    ([2],[2]) ∈ (trunkPlanAt (trunkCatalog.states k) pi).labels ∧
    (trunkPlanAt (trunkCatalog.states k) pi).labels.getLast? = some ([3],[2]) := by
  rcases hd with ⟨hm,h3,h9,hL,hR,h16,hRstar⟩
  let C := (trunkCatalog.states k).context
  have hCL : ¬ lowerEnds C.words.1 [3,1] := by
    intro hc
    apply hL
    exact hf.1.2.2.mpr hc
  have hCR : lowerEnds C.words.2 [3,1] := hf.2.1.2.2.mp hR
  change ¬ ([3,1] : List ℕ+) <:+ C.words.1 at hCL
  change ([3,1] : List ℕ+) <:+ C.words.2 at hCR
  let plan : TrunkPlan := ⟨[lowerHistoryH7,lowerHistoryH9,trunkH18],
    [([1],[]),([2],[]),([2],[2]),([3],[2])],
    [((([2],[2]) : LowerLabel),([3],[2]))]⟩
  have hpmem : plan ∈ trunkSourcePlans C := by
    unfold trunkSourcePlans
    simp [plan,hCL,hCR]
  obtain ⟨pi,hpi⟩ := List.mem_iff_getElem?.mp hpmem
  have hpilt : pi < (trunkSourcePlans C).length :=
    List.getElem?_eq_some_iff.mp hpi |>.1
  have hplan : trunkPlanAt (trunkCatalog.states k) pi = plan := by
    simp [trunkPlanAt,C,hpi]
  have hcuts : trunkHolds plan.cuts (lowerRatio (lowerNormalize p).1)
      (lowerRatio (lowerNormalize p).2) (lowerScale (lowerNormalize p)) := by
    simpa [plan] using small_marked_cuts p h3 h9 h16
  refine ⟨pi, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [C] using hpilt
  · simpa [hplan] using hcuts
  · simp [hplan,plan]
  · simp [hplan,plan]
  · simp [hplan,plan]

#print axioms solution
