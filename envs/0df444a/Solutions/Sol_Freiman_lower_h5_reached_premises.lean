-- Prove2me | solution 1 for Freiman.lower_h5_reached_premises
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-12T20:47:46.354791+00:00
-- url     : https://prove2.me/submissions/64c2e76d-48f8-49cf-b386-a492668508ef

import Definitions.Def_Freiman_lowerH5Verification
import Theorems.Thm_Freiman_continuant_denominator_pos
import Theorems.Thm_Freiman_lowerHistory_theta_values
import Mathlib.Tactic
import Definitions.Def_Freiman_lowerH5Model
import Theorems.Thm_Freiman_lowerEarlyTerminal_ratio_range
import Theorems.Thm_Freiman_lowerEarlyTerminal_ratio_append

open Freiman
attribute [local instance] Classical.propDecidable

private theorem cd_eq (w : List ℕ+) :
    lowerCD w = (wordContinuantPrevQ w, wordContinuantQ w) := by
  have h : ∀ (v : List ℕ) (m : (ℕ × ℕ) × (ℕ × ℕ)),
      (v.foldl (fun d a => ((d.1.2, (a : ℕ) * d.1.2 + d.1.1),
        (d.2.2, (a : ℕ) * d.2.2 + d.2.1))) m).2 =
      v.foldl (fun z a => (z.2, z.1 + (a : ℕ) * z.2)) m.2 := by
    intro v
    induction v with
    | nil => intro m; rfl
    | cons a v ih =>
      intro m
      simp only [List.foldl_cons]
      rw [ih]
      simp only [Nat.add_comm]
  simpa [lowerCD, wordContinuantPrevQ, wordContinuantQ, wordContinuantData]
    using (h (w.flatMap fun a => [(a : ℕ)]) ((1,0),(0,1))).symm

private theorem q_pos (w : List ℕ+) : 0 < ((lowerCD w).2 : ℝ) := by
  rw [cd_eq]
  exact_mod_cast continuant_denominator_pos w

private theorem threshold_value (c : CertField) (x y : CertField × CertField) (r s : ℝ) :
    certThresholdVal (lowerHistoryThreshold c x y) r s =
      certFieldVal c * ((1+s*certFieldVal y.1)*(1+s*certFieldVal y.2)) /
        ((1+r*certFieldVal x.1)*(1+r*certFieldVal x.2)) := by
  simp only [lowerHistoryThreshold, lowerHistorySort]
  split <;> split <;>
    simp only [certThresholdVal, certThresholdNum, certThresholdDen] <;> ring

private theorem normalize_wide (p : LowerPair) :
    lowerWidth (lowerNormalize p).2 ≤ lowerWidth (lowerNormalize p).1 := by
  unfold lowerNormalize
  split_ifs with h
  · exact h
  · exact (lt_of_not_ge h).le

private theorem h5_normalize_idem (p : LowerPair) :
    lowerNormalize (lowerNormalize p) = lowerNormalize p := by
  conv_lhs => rw [lowerNormalize]
  exact if_pos (normalize_wide p)

private theorem normalize_good (p : LowerPair) (h : lowerGood p) : lowerGood (lowerNormalize p) := by
  simpa only [lowerGood, lowerChild, h5_normalize_idem] using h

private theorem normalize_box (p : LowerPair) (h : lowerParameterBox p) :
    lowerParameterBox (lowerNormalize p) := by
  unfold lowerNormalize
  split_ifs
  · exact h
  · exact ⟨h.2.2.1,h.2.2.2,h.1,h.2.1⟩

private theorem hn_holds (hw : LowerHistoryWidthLaw) (p : LowerPair) :
    lowerHistoryAtBase (lowerNormalize p) [lowerHistoryHN] := by
  have h := (hw (lowerNormalize p) ([],[])).1.mp (by simpa using normalize_wide p)
  exact h

private theorem zero_holds (p : LowerPair) : lowerHistoryAtBase p [lowerHistoryZero] := by
  have hq1 := q_pos p.1
  have hq2 := q_pos p.2
  have hs : 0 < lowerScale p := by unfold lowerScale; positivity
  simpa [lowerHistoryAtBase, lowerHistoryConditions, lowerHistoryZero,
    lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryRat,
    certBoundHolds, certThresholdVal, certThresholdNum, certThresholdDen, certFieldVal] using hs

private theorem h2_value (p : LowerPair) :
    certThresholdVal lowerHistoryH2.threshold
      (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2) =
      lowerThreshold p (37/50) 63 70 66 90 := by
  simp only [lowerHistoryH2, lowerHistoryPB, threshold_value, lowerThreshold,
    lowerHistory_theta_values 63 (by simp), lowerHistory_theta_values 70 (by simp),
    lowerHistory_theta_values 66 (by simp), lowerHistory_theta_values 90 (by simp)]
  norm_num [lowerHistoryRat, certFieldVal]

private theorem h5_value (p : LowerPair) :
    certThresholdVal lowerHistoryH5.threshold
      (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2) =
      lowerThreshold p (279/500) 35 63 63 70 := by
  simp only [lowerHistoryH5, lowerHistoryPB, threshold_value, lowerThreshold,
    lowerHistory_theta_values 35 (by simp), lowerHistory_theta_values 63 (by simp),
    lowerHistory_theta_values 70 (by simp)]
  norm_num [lowerHistoryRat, certFieldVal]

private theorem active_bounds (p : LowerPair) (ha : lowerH5Active p) :
    lowerHistoryAtBase (lowerNormalize p)
      [lowerHistoryComplement lowerHistoryH2,lowerHistoryH5] := by
  have h2 := ha.2.1
  have h5 := ha.2.2.1
  change ¬ lowerThreshold p (37/50) 63 70 66 90 < lowerScale (lowerNormalize p) at h2
  change lowerScale (lowerNormalize p) < lowerThreshold p (279/500) 35 63 63 70 at h5
  rw [← h2_value p] at h2
  rw [← h5_value p] at h5
  simp only [lowerHistoryAtBase, lowerHistoryConditions, List.mem_cons,
    forall_eq_or_imp, List.not_mem_nil, IsEmpty.forall_iff, and_true,
    lowerHistoryComplement, lowerHistoryH2, lowerHistoryH5, lowerHistoryPB,
    certBoundHolds, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  exact ⟨le_of_not_gt h2,h5,by simp⟩

private def pull_ok (b : CertBound) : Prop :=
    0 < certFieldVal b.threshold.c ∧
    0 ≤ certFieldVal b.threshold.x0 ∧ 0 ≤ certFieldVal b.threshold.x1 ∧
    0 ≤ certFieldVal b.threshold.y0 ∧ 0 ≤ certFieldVal b.threshold.y1

private theorem threshold_ok (lo strict : Bool) (c : CertField) (x y : CertField × CertField)
    (hc : 0 < certFieldVal c)
    (hx : 0 ≤ certFieldVal x.1 ∧ 0 ≤ certFieldVal x.2)
    (hy : 0 ≤ certFieldVal y.1 ∧ 0 ≤ certFieldVal y.2) :
    pull_ok ⟨lo,strict,lowerHistoryThreshold c x y⟩ := by
  simp only [pull_ok,lowerHistoryThreshold,lowerHistorySort]
  split <;> split <;> simp_all

private theorem wh_empty : lowerHistoryWH ([],[]) =
    ⟨lowerHistoryRat 1,lowerHistoryBeta,lowerHistoryAlpha,lowerHistoryBeta,lowerHistoryAlpha⟩ := by
  norm_num [lowerHistoryWH,lowerHistoryCF,lowerHistoryMatrix,lowerHistoryDiv,
    lowerHistoryAbs,lowerHistoryNeg,lowerHistorySign,lowerHistoryQuadSign,
    lowerHistoryRatSign,lowerHistoryInv,lowerHistoryThreshold,lowerHistorySort,
    lowerHistoryLex,lowerHistoryRat,lowerHistoryAlpha,lowerHistoryBeta,
    certFieldScale,certFieldMul,certFieldAdd,certFieldSub]

private theorem tail_nonnegative : 0 ≤ lowerAlpha ∧ 0 ≤ lowerBeta ∧ 0 ≤ lowerTau := by
  have h21 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 21)
  have h3 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have n21 := Real.sqrt_nonneg (21:ℝ)
  have n3 := Real.sqrt_nonneg (3:ℝ)
  dsimp [lowerAlpha,lowerBeta,lowerTau]
  constructor
  · nlinarith
  constructor <;> nlinarith

private theorem pe_nonnegative (w : List ℕ+) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ prefixEval w x := by
  induction w with
  | nil => exact hx
  | cons a w ih => simp only [prefixEval]; positivity

private theorem theta_nonnegative (i : ℕ)
    (hi : i ∈ [35,63,66,70,90]) : 0 ≤ certFieldVal (lowerHistoryTheta i) := by
  have hh : i ∈ ([3,20,22,25,28,35,36,63,65,66,68,70,90,94] : List ℕ) := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; tauto
  rw [lowerHistory_theta_values i hh]
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl <;>
    exact pe_nonnegative _ _ tail_nonnegative.2.2

private theorem pulled_bounds_ok (b : CertBound)
    (hb : b ∈ [lowerHistoryHN,lowerHistoryComplement lowerHistoryH2,lowerHistoryH5]) :
    pull_ok b := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl
  · simp only [lowerHistoryHN,wh_empty,pull_ok]
    have ha : 0 ≤ certFieldVal lowerHistoryAlpha := by
      have ht := tail_nonnegative.1
      dsimp [lowerAlpha] at ht
      norm_num [certFieldVal,lowerHistoryAlpha]
      linarith
    have hb : 0 ≤ certFieldVal lowerHistoryBeta := by
      have ht := tail_nonnegative.2.1
      dsimp [lowerBeta] at ht
      norm_num [certFieldVal,lowerHistoryBeta]
      linarith
    exact ⟨by norm_num [certFieldVal,lowerHistoryRat],hb,ha,hb,ha⟩
  · apply threshold_ok
    · norm_num [certFieldVal,lowerHistoryRat]
    · exact ⟨theta_nonnegative 63 (by simp),theta_nonnegative 66 (by simp)⟩
    · exact ⟨theta_nonnegative 70 (by simp),theta_nonnegative 90 (by simp)⟩
  · apply threshold_ok
    · norm_num [certFieldVal,lowerHistoryRat]
    · exact ⟨theta_nonnegative 35 (by simp),theta_nonnegative 63 (by simp)⟩
    · exact ⟨theta_nonnegative 63 (by simp),theta_nonnegative 70 (by simp)⟩



private theorem at_append (base : LowerPair) (xs ys : List CertBound) :
    lowerHistoryAtBase base (xs++ys) ↔
      lowerHistoryAtBase base xs ∧ lowerHistoryAtBase base ys := by
  simp only [lowerHistoryAtBase,lowerHistoryConditions,List.mem_append,
    or_imp, forall_and]

private theorem h5_reached_from_rectangle
    (hrect : ∀ (w ctx : List ℕ+), lowerEnds w ctx →
      (1/4:ℝ) ≤ lowerRatio w → lowerRatio w ≤ 4/5 →
      ((lowerH5ContextBox ctx).1:ℝ) ≤ lowerRatio w ∧
        lowerRatio w ≤ ((lowerH5ContextBox ctx).2:ℝ))
    (hg : LowerHistoryGoodnessLaw) (hpull : LowerHistoryPullLaw) (hwidth : LowerHistoryWidthLaw)
    (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n)
    (ha : lowerH5Active (h n)) (c : LowerH5Case) (hshape : lowerH5CaseShape c)
    (hc : lowerH5Immediate h n c) : lowerH5ReachedPremises h n c := by
  rcases hc with ⟨m,hm,hfit,hphysical,hnormal,hcuts⟩
  have hs := hh.2.1 m (by omega)
  let base := lowerNormalize (h m)
  have hb := normalize_box (h m) hs.2.2.2
  have hr := hrect base.1 c.context.words.1 hfit.1.1 hb.1 hb.2.1
  have hs' := hrect base.2 c.context.words.2 hfit.2.1.1 hb.2.2.1 hb.2.2.2
  have hrectangle : certRectangleMem c.rectangle (lowerRatio base.1) (lowerRatio base.2) := by
    rw [hshape.2.2.2.2.1]
    exact ⟨hr.1,hr.2,hs'.1,hs'.2⟩
  obtain ⟨bs,hbs,hgood⟩ := hg base c.context hfit (h5_normalize_idem (h m))
    (normalize_good (h m) hs.2.1)
  have hgood' : lowerHistoryAtBase base ((lowerHistoryRelaxedGoodness c.context).getD []) := by
    simpa [hbs] using hgood
  have hstart : lowerHistoryAtBase base [lowerHistoryZero,lowerHistoryHN] := by
    have h0 := zero_holds base
    have hN := hn_holds hwidth (h m)
    exact (at_append base [lowerHistoryZero] [lowerHistoryHN]).mpr ⟨h0,hN⟩
  have hnow : lowerHistoryAtBase (lowerNormalize (h n))
      [lowerHistoryHN,lowerHistoryComplement lowerHistoryH2,lowerHistoryH5] := by
    exact (at_append _ [lowerHistoryHN] _).mpr
      ⟨hn_holds hwidth (h n),active_bounds (h n) ha⟩
  have hmap : lowerHistoryAtBase base
      ([lowerHistoryHN,lowerHistoryComplement lowerHistoryH2,lowerHistoryH5].map
        (fun b => lowerHistoryPull b c.words c.reflect)) := by
    intro b hb
    obtain ⟨a,ha',rfl⟩ := List.mem_map.mp hb
    have ho := pulled_bounds_ok a ha'
    refine ((hpull base c.words a c.reflect ho.1 ho.2.1 ho.2.2.1 ho.2.2.2.1 ho.2.2.2.2).mp ?_) _ (by simp)
    have hsingle : lowerHistoryAtBase (lowerNormalize (h n)) [a] := by
      intro d hd
      have he : d = a := List.mem_singleton.mp hd
      subst d
      exact hnow a ha'
    rw [hnormal] at hsingle
    rw [hphysical] at hsingle
    exact hsingle
  refine ⟨m,hm,hrectangle,?_⟩
  unfold lowerH5Premises
  rw [at_append,at_append,at_append]
  exact ⟨⟨⟨hstart,hcuts⟩,hgood'⟩,hmap⟩


private theorem h5_prefixEval_snoc (a : ℕ+) (ys : List ℕ+) (x : ℝ) :
    prefixEval (ys ++ [a]) x = prefixEval ys (1 / ((a : ℝ) + x)) := by
  induction ys with
  | nil => rfl
  | cons b ys ih => simp only [List.cons_append,prefixEval,ih]


private theorem boxFold_bounds : ∀ (ctx : List ℕ+) (z : ℚ × ℚ) (x : ℝ),
    0 ≤ (z.1 : ℝ) → (z.1 : ℝ) ≤ x → x ≤ (z.2 : ℝ) →
    let v := ctx.foldl (fun z (a : ℕ) => (1 / ((a : ℚ) + z.2), 1 / ((a : ℚ) + z.1))) z
    (v.1 : ℝ) ≤ prefixEval ctx.reverse x ∧
      prefixEval ctx.reverse x ≤ (v.2 : ℝ) := by
  intro ctx
  induction ctx with
  | nil =>
      intro z x hz hlo hhi
      exact ⟨hlo, hhi⟩
  | cons a ctx ih =>
      intro z x hz hlo hhi
      simp only [List.reverse_cons, h5_prefixEval_snoc]
      apply ih
      · dsimp only
        push_cast
        have ha : (1 : ℝ) ≤ ((a : ℕ) : ℝ) := by
          exact_mod_cast (Nat.succ_le_of_lt (PNat.pos a))
        exact one_div_nonneg.mpr (by linarith)
      · dsimp only
        push_cast
        apply one_div_le_one_div_of_le
        · have ha : (1 : ℝ) ≤ ((a : ℕ) : ℝ) := by
            exact_mod_cast (Nat.succ_le_of_lt (PNat.pos a))
          linarith
        · linarith
      · dsimp only
        push_cast
        apply one_div_le_one_div_of_le
        · have ha : (1 : ℝ) ≤ ((a : ℕ) : ℝ) := by
            exact_mod_cast (Nat.succ_le_of_lt (PNat.pos a))
          linarith
        · linarith

private theorem ratio_in_context_box (w ctx : List ℕ+)
    (he : lowerEnds w ctx)
    (hlo : (1 / 4 : ℝ) ≤ lowerRatio w)
    (hhi : lowerRatio w ≤ (4 / 5 : ℝ)) :
    ((lowerH5ContextBox ctx).1 : ℝ) ≤ lowerRatio w ∧
      lowerRatio w ≤ ((lowerH5ContextBox ctx).2 : ℝ) := by
  unfold lowerEnds at he
  rcases he with ⟨u, rfl⟩
  have hrange := lowerEarlyTerminal_ratio_range u
  have hfold := boxFold_bounds ctx ((0, 1) : ℚ × ℚ) (lowerRatio u)
      (by norm_num) (by simpa using hrange.1) (by simpa using hrange.2)
  rw [lowerEarlyTerminal_ratio_append] at hlo hhi ⊢
  simpa only [lowerH5ContextBox, Rat.cast_max, Rat.cast_min,
    Rat.cast_ofNat, Rat.cast_div, Rat.cast_one] using
    And.intro (max_le hlo hfold.1) (le_min hhi hfold.2)


theorem solution (hg : LowerHistoryGoodnessLaw) (hpull : LowerHistoryPullLaw) (hwidth : LowerHistoryWidthLaw)
    (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n)
    (ha : lowerH5Active (h n)) (c : LowerH5Case) (hshape : lowerH5CaseShape c)
    (hc : lowerH5Immediate h n c) : lowerH5ReachedPremises h n c := by
  exact h5_reached_from_rectangle ratio_in_context_box hg hpull hwidth t h n hh ha c hshape hc

#print axioms solution
