-- Prove2me | solution 1 for Freiman.trunk_select_geometry_equal_open
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-12T20:37:57.322367+00:00
-- url     : https://prove2.me/submissions/f492b4f4-4152-4043-aaee-0f967f3dc7a5

import Definitions.Def_Freiman_trunkGeometry
import Theorems.Thm_Freiman_lowerHistory_theta_values
import Mathlib.Tactic

open Freiman
attribute [local instance] Classical.propDecidable

private theorem threshold_value (c : CertField) (x y : CertField × CertField) (r s : ℝ) :
    certThresholdVal (lowerHistoryThreshold c x y) r s =
      certFieldVal c * ((1+s*certFieldVal y.1)*(1+s*certFieldVal y.2)) /
        ((1+r*certFieldVal x.1)*(1+r*certFieldVal x.2)) := by
  simp only [lowerHistoryThreshold, lowerHistorySort]
  split <;> split <;>
    simp only [certThresholdVal, certThresholdNum, certThresholdDen] <;> ring

private theorem first_plan (C : LowerHistoryContext) :
    (trunkSourcePlans C)[0]? = some
      ⟨[lowerHistoryComplement lowerHistoryH7],
        [([1],[]),([2],[])] ++
          (if lowerEnds C.words.1 [3,1] then [] else [([3],[])]), []⟩ := by
  classical
  by_cases hL : lowerEnds C.words.1 [3,1] <;>
    by_cases hR : lowerEnds C.words.2 [3,1] <;>
      simp [trunkSourcePlans, lowerEnds] at hL hR ⊢ <;>
      simp [hL, hR]

private theorem first_plan_length (C : LowerHistoryContext) :
    0 < (trunkSourcePlans C).length := by
  have h := first_plan C
  by_contra hn
  have he : trunkSourcePlans C = [] := List.eq_nil_of_length_eq_zero (by omega)
  simp [he] at h

private theorem strictGood_good (p : LowerPair) (h : lowerStrictGood p) : lowerGood p := by
  rcases lt_min_iff.mp h with ⟨h1,h2⟩
  rw [lowerGood, lowerCover]
  refine ⟨max (lowerEndpoint (lowerChild p ([1], [])) false)
    (lowerEndpoint (lowerChild p ([2], [])) false), ?_⟩
  exact ⟨⟨le_max_left _ _, h1.le⟩,
    ⟨le_max_right _ _, h2.le⟩⟩

private theorem local_membership (p : LowerPair) (l : LowerLabel) (t : ℝ) :
    t ∈ lowerCover (lowerChild p l) ↔
      lowerLocalLower p l ≤ lowerLocalCoordinate p t ∧
      lowerLocalCoordinate p t ≤ trunkLocalUpper p l := by
  unfold lowerCover lowerLocalLower lowerLocalCoordinate trunkLocalUpper
  split_ifs <;> simp only [Set.mem_Icc, neg_le_neg_iff]
  exact and_comm

private theorem local_contact (p : LowerPair) (l m : LowerLabel)
    (h : (lowerCover (lowerChild p l) ∩ lowerCover (lowerChild p m)).Nonempty) :
    lowerLocalLower p l ≤ trunkLocalUpper p m := by
  rcases h with ⟨t, hl, hm⟩
  exact le_trans ((local_membership p l t).mp hl).1
    ((local_membership p m t).mp hm).2

private theorem short_plan_select (t : ℝ) (p : LowerPair) (hasThird : Bool) (cuts : List CertBound)
    (hp : t ∈ lowerCover p)
    (hg : TrunkGeometry p ⟨cuts, [([1],[]),([2],[])] ++
        (if hasThird then [([3],[])] else []), []⟩) :
    ∃ l ∈ ([([1],[]),([2],[])] ++ (if hasThird then [([3],[])] else [])),
      lowerGood (lowerChild p l) ∧ t ∈ lowerCover (lowerChild p l) := by
  have hparent : trunkParentEndpoint p false ≤ lowerLocalCoordinate p t ∧
      lowerLocalCoordinate p t ≤ trunkParentEndpoint p true := by
    unfold trunkParentEndpoint lowerLocalCoordinate
    change lowerEndpoint p false ≤ t ∧ t ≤ lowerEndpoint p true at hp
    split_ifs <;> simpa only [Bool.not_false, Bool.not_true, neg_le_neg_iff, and_comm] using hp
  have hu := le_trans hparent.2 (hg.upper ([1],[]) (by cases hasThird <;> rfl))
  have h12 := local_contact p ([1],[]) ([2],[]) (hg.contacts (([1],[]),([2],[]))
    (by cases hasThird <;> simp) (by simp))
  cases hasThird
  · have hl := le_trans (hg.lower ([2],[]) (by rfl)) hparent.1
    by_cases ht : lowerLocalCoordinate p t ≤ trunkLocalUpper p ([2],[])
    · exact ⟨([2],[]), by simp, strictGood_good _ (hg.strictGood _ (by simp)),
        (local_membership p _ t).mpr ⟨hl,ht⟩⟩
    · exact ⟨([1],[]), by simp, strictGood_good _ (hg.strictGood _ (by simp)),
        (local_membership p _ t).mpr ⟨le_trans h12 (le_of_lt (lt_of_not_ge ht)),hu⟩⟩
  · have hl := le_trans (hg.lower ([3],[]) (by rfl)) hparent.1
    have h23 := local_contact p ([2],[]) ([3],[]) (hg.contacts (([2],[]),([3],[]))
      (by simp) (by simp))
    by_cases ht3 : lowerLocalCoordinate p t ≤ trunkLocalUpper p ([3],[])
    · exact ⟨([3],[]), by simp, strictGood_good _ (hg.strictGood _ (by simp)),
        (local_membership p _ t).mpr ⟨hl,ht3⟩⟩
    · by_cases ht2 : lowerLocalCoordinate p t ≤ trunkLocalUpper p ([2],[])
      · exact ⟨([2],[]), by simp, strictGood_good _ (hg.strictGood _ (by simp)),
          (local_membership p _ t).mpr ⟨le_trans h23 (le_of_lt (lt_of_not_ge ht3)),ht2⟩⟩
      · exact ⟨([1],[]), by simp, strictGood_good _ (hg.strictGood _ (by simp)),
          (local_membership p _ t).mpr ⟨le_trans h12 (le_of_lt (lt_of_not_ge ht2)),hu⟩⟩



private theorem h7_value (p : LowerPair) :
    certThresholdVal lowerHistoryH7.threshold
      (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2) =
      lowerThreshold p (31/100) 3 63 25 66 := by
  simp only [lowerHistoryH7, lowerHistoryPB, threshold_value, lowerThreshold,
    lowerHistory_theta_values 3 (by simp), lowerHistory_theta_values 25 (by simp),
    lowerHistory_theta_values 63 (by simp), lowerHistory_theta_values 66 (by simp)]
  norm_num [lowerHistoryRat, certFieldVal]

private theorem open_select (t : ℝ) (p : LowerPair) (hs : lowerState t p)
    (hc : ¬ lowerMixed p ∧ lowerA p 3) (hg : TrunkActiveGeometry p) :
    lowerNumericSuccessor t p := by
  classical
  rcases hg with ⟨k, hf, hr, hg⟩
  let C := (trunkCatalog.states k).context
  have hcut : trunkHolds [lowerHistoryComplement lowerHistoryH7]
      (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2)
      (lowerScale (lowerNormalize p)) := by
    have ha := hc.2
    change lowerScale (lowerNormalize p) < lowerThreshold p (31/100) 3 63 25 66 at ha
    rw [← h7_value p] at ha
    simpa only [trunkHolds, lowerHistoryConditions, List.mem_singleton,
      forall_eq, lowerHistoryComplement, lowerHistoryH7, lowerHistoryPB,
      Bool.not_true, Bool.not_false, certBoundHolds, Bool.false_eq_true, ↓reduceIte] using ha
  have hplan : trunkPlanAt (trunkCatalog.states k) 0 =
      ⟨[lowerHistoryComplement lowerHistoryH7],
        [([1],[]),([2],[])] ++
          (if lowerL p then [] else [([3],[])]), []⟩ := by
    unfold trunkPlanAt
    rw [first_plan C]
    simp only [Option.getD_some]
    have hL := hf.1.2.2
    change (lowerL p ↔ lowerEnds C.words.1 [3,1]) at hL
    simp only [hL]
  have hgeom := hg 0 (first_plan_length C) (by simpa [hplan] using hcut)
  rw [hplan] at hgeom
  have hgeom' : TrunkGeometry p ⟨[lowerHistoryComplement lowerHistoryH7], [([1],[]),([2],[])] ++
      (if decide (¬ lowerL p) then [([3],[])] else []), []⟩ := by
    by_cases hL : lowerL p <;> simpa [hL] using hgeom
  obtain ⟨l,hl,hgood,ht⟩ := short_plan_select t p (decide (¬ lowerL p)) _ hs.2.2.1 hgeom'
  apply Or.inr
  refine ⟨l, ?_, hgood, ht⟩
  apply Or.inl
  simpa [lowerEqualList, hc.1, hc.2] using hl



theorem solution (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hb : lowerSuffixBounds p t)
    (hp97 : lowerP97Anchor p t) (hlate : lowerLateEntryDomain p)
    (hc : ¬ lowerMixed p ∧ lowerA p 3)
    (hg : TrunkActiveGeometry p) :
    lowerNumericSuccessor t p := by
  exact open_select t p hs hc hg

#print axioms solution
