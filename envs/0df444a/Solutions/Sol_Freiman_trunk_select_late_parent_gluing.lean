-- Prove2me | solution 1 for Freiman.trunk_select_late_parent_gluing
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-13T19:55:43.25878+00:00
-- url     : https://prove2.me/submissions/9ad7bdc6-a71d-4756-a209-ac24abc6c711

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Basic

set_option maxHeartbeats 1000000
set_option maxRecDepth 40000

open Freiman

namespace M7Last

/-- Walking down a chain of overlapping intervals. -/
lemma walk {α : Type*} (lo hi : α → ℝ) (Rel : α → α → Prop)
    (hR : ∀ a b, Rel a b → lo a ≤ hi b) (x : ℝ) :
    ∀ (L : List α), L ≠ [] → List.IsChain Rel L →
      (∀ a, L.head? = some a → x ≤ hi a) →
      (∀ a, L.getLast? = some a → lo a ≤ x) →
      ∃ a ∈ L, lo a ≤ x ∧ x ≤ hi a
  | [], h, _, _, _ => absurd rfl h
  | [a], _, _, hh, hl => ⟨a, by simp, hl a (by simp), hh a (by simp)⟩
  | a :: b :: t, _, hchain, hh, hl => by
      by_cases hx : lo a ≤ x
      · exact ⟨a, by simp, hx, hh a (by simp)⟩
      · have hab : Rel a b := (List.isChain_cons_cons.mp hchain).1
        have hxb : x ≤ hi b := le_trans (le_of_lt (not_le.mp hx)) (hR a b hab)
        obtain ⟨c, hc, h1, h2⟩ :=
          walk lo hi Rel hR x (b :: t) (by simp) (List.isChain_cons_cons.mp hchain).2
            (fun a' ha' => by simp only [List.head?_cons, Option.some.injEq] at ha'; exact ha' ▸ hxb)
            (fun a' ha' => hl a' (by rw [List.getLast?_cons_cons]; exact ha'))
        exact ⟨c, List.mem_cons_of_mem _ hc, h1, h2⟩

lemma zip_of_chain {α : Type*} (R : α → α → Prop) : ∀ (l : List α),
    List.IsChain R l → ∀ x ∈ l.zip l.tail, R x.1 x.2
  | [], _ => by simp
  | [_], _ => by simp
  | a :: b :: t, h => by
      intro x hx
      rw [List.isChain_cons_cons] at h
      simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact h.1
      · exact zip_of_chain R (b :: t) h.2 x (by simpa using hx)

end M7Last

theorem solution (hroute : ∀ (t : ℝ) (p : LowerPair), lowerState t p → (¬ lowerMixed p ∧ ¬ lowerA p 3 ∧ ¬ lowerA p 9 ∧ lowerL p ∧ ¬ lowerLStar p) → lowerLateEntryDomain p → ∃ ls : List LowerLabel, lowerLateRouteValid p ls)
    (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hb : lowerSuffixBounds p t)
    (hp97 : lowerP97Anchor p t) (hlate : lowerLateEntryDomain p)
    (hc : ¬ lowerMixed p ∧ ¬ lowerA p 3 ∧ ¬ lowerA p 9 ∧ lowerL p)
    (hg : TrunkActiveGeometry p) :
    lowerNumericSuccessor t p := by
  classical
  obtain ⟨hadm, hgoodp, hcov, hbox⟩ := hs
  obtain ⟨k, hfit, _hrect, hgeom⟩ := hg
  -- ============ the three source plans of a left-marked context ============
  have hL : ([3,1] : List ℕ+).IsSuffix (trunkCatalog.states k).context.words.1 :=
    hfit.1.2.2.mp hc.2.2.2
  have hplans : trunkSourcePlans (trunkCatalog.states k).context =
      [⟨[lowerHistoryComplement lowerHistoryH7], [([1],[]),([2],[])], []⟩,
       ⟨[lowerHistoryH7,lowerHistoryH9], [([1],[]),([2],[])], []⟩,
       ⟨[lowerHistoryH7,lowerHistoryComplement lowerHistoryH9],
        [([1],[]),([2],[1]),([2],[2]),([2],[3])],
        [((([2],[1]) : LowerLabel),(([2],[2]) : LowerLabel))]⟩] := by
    simp [trunkSourcePlans, hL]
  have hpa : trunkPlanAt (trunkCatalog.states k) 2 =
      ⟨[lowerHistoryH7,lowerHistoryComplement lowerHistoryH9],
       [([1],[]),([2],[1]),([2],[2]),([2],[3])],
       [((([2],[1]) : LowerLabel),(([2],[2]) : LowerLabel))]⟩ := by
    simp [trunkPlanAt, hplans]
  -- ============ the two cuts of that plan hold ============
  have hsq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hnn : (0:ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have h1 : (1:ℝ) < Real.sqrt 3 := by nlinarith
  have h2 : Real.sqrt 3 < (2:ℝ) := by nlinarith
  have e0 : (3:ℝ) + (Real.sqrt 3 - 1) = 2 + Real.sqrt 3 := by ring
  have e1 : (1:ℝ) / (2 + Real.sqrt 3) = 2 - Real.sqrt 3 := by
    rw [div_eq_iff (by nlinarith)]; nlinarith
  have t3 : lowerTheta 3 = 2 - Real.sqrt 3 := by
    show prefixEval [3] lowerTau = _
    simp only [prefixEval, lowerTau]; push_cast; rw [e0, e1]
  have t25 : lowerTheta 25 = (5 + Real.sqrt 3) / 22 := by
    show prefixEval [3,3] lowerTau = _
    simp only [prefixEval, lowerTau]; push_cast
    rw [e0, e1, show (3:ℝ) + (2 - Real.sqrt 3) = 5 - Real.sqrt 3 by ring,
      div_eq_iff (by nlinarith)]
    nlinarith
  have t63 : lowerTheta 63 = (4 + Real.sqrt 3) / 13 := by
    show prefixEval [2,3] lowerTau = _
    simp only [prefixEval, lowerTau]; push_cast
    rw [e0, e1, show (2:ℝ) + (2 - Real.sqrt 3) = 4 - Real.sqrt 3 by ring,
      div_eq_iff (by nlinarith)]
    nlinarith
  have t66 : lowerTheta 66 = (9 - Real.sqrt 3) / 13 := by
    show prefixEval [1,1,3] lowerTau = _
    simp only [prefixEval, lowerTau]; push_cast
    rw [e0, e1, show (1:ℝ) + (2 - Real.sqrt 3) = 3 - Real.sqrt 3 by ring,
      show (1:ℝ) / (3 - Real.sqrt 3) = (3 + Real.sqrt 3) / 6 by
        rw [div_eq_div_iff (by nlinarith) (by norm_num)]; nlinarith,
      show (1:ℝ) + (3 + Real.sqrt 3) / 6 = (9 + Real.sqrt 3) / 6 by ring,
      div_div_eq_mul_div, one_mul, div_eq_div_iff (by nlinarith) (by norm_num)]
    nlinarith
  have t36 : lowerTheta 36 = (Real.sqrt 3 - 1) / 2 := by
    show prefixEval [] (lowerTau / 2) = _
    simp only [prefixEval, lowerTau]
  have cfl : ∀ q : ℚ, certFieldVal (lowerHistoryRat q) = (q : ℝ) := by
    intro q; simp [certFieldVal, lowerHistoryRat]
  have hT3 : lowerHistoryTheta 3 = (⟨2,-1,0,0⟩ : CertField) := by
    norm_num [lowerHistoryTheta, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryDiv,
      lowerHistoryInv, certFieldMul, certFieldAdd, certFieldScale, lowerHistoryRat,
      lowerHistoryTau, CertField.mk.injEq]
  have hT25 : lowerHistoryTheta 25 = (⟨5/22,1/22,0,0⟩ : CertField) := by
    norm_num [lowerHistoryTheta, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryDiv,
      lowerHistoryInv, certFieldMul, certFieldAdd, certFieldScale, lowerHistoryRat,
      lowerHistoryTau, CertField.mk.injEq]
  have hT63 : lowerHistoryTheta 63 = (⟨4/13,1/13,0,0⟩ : CertField) := by
    norm_num [lowerHistoryTheta, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryDiv,
      lowerHistoryInv, certFieldMul, certFieldAdd, certFieldScale, lowerHistoryRat,
      lowerHistoryTau, CertField.mk.injEq]
  have hT66 : lowerHistoryTheta 66 = (⟨9/13,-1/13,0,0⟩ : CertField) := by
    norm_num [lowerHistoryTheta, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryDiv,
      lowerHistoryInv, certFieldMul, certFieldAdd, certFieldScale, lowerHistoryRat,
      lowerHistoryTau, CertField.mk.injEq]
  have hT36 : lowerHistoryTheta 36 = (⟨-1/2,1/2,0,0⟩ : CertField) := by
    norm_num [lowerHistoryTheta, certFieldScale, lowerHistoryTau, CertField.mk.injEq]
  have v3 : certFieldVal (lowerHistoryTheta 3) = lowerTheta 3 := by
    rw [hT3, t3]; simp [certFieldVal]; push_cast; ring
  have v25 : certFieldVal (lowerHistoryTheta 25) = lowerTheta 25 := by
    rw [hT25, t25]; simp [certFieldVal]; push_cast; ring
  have v63 : certFieldVal (lowerHistoryTheta 63) = lowerTheta 63 := by
    rw [hT63, t63]; simp [certFieldVal]; push_cast; ring
  have v66 : certFieldVal (lowerHistoryTheta 66) = lowerTheta 66 := by
    rw [hT66, t66]; simp [certFieldVal]; push_cast; ring
  have v36 : certFieldVal (lowerHistoryTheta 36) = lowerTheta 36 := by
    rw [hT36, t36]; simp [certFieldVal]; push_cast; ring
  have thr : ∀ (c a b u v : CertField) (r s : ℝ),
      certThresholdVal (lowerHistoryThreshold c (a,b) (u,v)) r s
        = certFieldVal c * ((1+s*certFieldVal u) * (1+s*certFieldVal v))
          / ((1+r*certFieldVal a) * (1+r*certFieldVal b)) := by
    intro c a b u v r s
    simp only [lowerHistoryThreshold, lowerHistorySort, certThresholdVal, certThresholdNum,
      certThresholdDen]
    split_ifs <;> ring
  have hA3 : lowerThreshold p (31/100) 3 63 25 66 ≤ lowerScale (lowerNormalize p) :=
    not_lt.mp hc.2.1
  have hA9 : lowerThreshold p ((3-Real.sqrt 3)/2) 36 63 63 66 < lowerScale (lowerNormalize p) :=
    not_le.mp hc.2.2.1
  have hcuts : trunkHolds
      [lowerHistoryH7, lowerHistoryComplement lowerHistoryH9]
      (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2)
      (lowerScale (lowerNormalize p)) := by
    intro b hb'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb'
    rcases hb' with rfl | rfl
    · show certThresholdVal (lowerHistoryThreshold (lowerHistoryRat (31/100))
        (lowerHistoryTheta 3, lowerHistoryTheta 25) (lowerHistoryTheta 63, lowerHistoryTheta 66))
        (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2)
        ≤ lowerScale (lowerNormalize p)
      rw [thr, cfl, v3, v25, v63, v66]
      refine le_trans (le_of_eq ?_) hA3
      simp only [lowerThreshold]; push_cast; ring
    · show certThresholdVal (lowerHistoryThreshold (⟨3/2,-1/2,0,0⟩ : CertField)
        (lowerHistoryTheta 36, lowerHistoryTheta 63) (lowerHistoryTheta 63, lowerHistoryTheta 66))
        (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2)
        < lowerScale (lowerNormalize p)
      rw [thr, v36, v63, v66]
      refine lt_of_le_of_lt (le_of_eq ?_) hA9
      simp only [lowerThreshold, certFieldVal]; push_cast; ring
  have hTG : TrunkGeometry p
      ⟨[lowerHistoryH7,lowerHistoryComplement lowerHistoryH9],
       [([1],[]),([2],[1]),([2],[2]),([2],[3])],
       [((([2],[1]) : LowerLabel),(([2],[2]) : LowerLabel))]⟩ := by
    have := hgeom 2 (by rw [hplans]; norm_num) (by rw [hpa]; exact hcuts)
    rwa [hpa] at this
  -- ============ local-coordinate dictionary ============
  have hF1 : ∀ l : LowerLabel, lowerLocalLower p l ≤ lowerLocalCoordinate p t →
      lowerLocalCoordinate p t ≤ trunkLocalUpper p l → t ∈ lowerCover (lowerChild p l) := by
    intro l ha hb'
    simp only [lowerLocalLower, trunkLocalUpper, lowerLocalCoordinate] at ha hb'
    show t ∈ Set.Icc _ _
    rw [Set.mem_Icc]
    by_cases hev : (lowerNormalize p).1.length % 2 = 0
    · simp only [hev, if_true] at ha hb'
      exact ⟨ha, hb'⟩
    · simp only [hev, if_false] at ha hb'
      constructor <;> linarith
  have hF2 : trunkParentEndpoint p false ≤ lowerLocalCoordinate p t ∧
      lowerLocalCoordinate p t ≤ trunkParentEndpoint p true := by
    have hcov' : lowerEndpoint p false ≤ t ∧ t ≤ lowerEndpoint p true := by
      have : t ∈ Set.Icc (lowerEndpoint p false) (lowerEndpoint p true) := hcov
      exact Set.mem_Icc.mp this
    simp only [trunkParentEndpoint, lowerLocalCoordinate]
    by_cases hev : (lowerNormalize p).1.length % 2 = 0
    · simp only [hev, if_true]
      exact ⟨hcov'.1, hcov'.2⟩
    · simp only [hev, if_false, Bool.not_false, Bool.not_true]
      constructor <;> linarith [hcov'.1, hcov'.2]
  have hF4 : ∀ l m : LowerLabel,
      (lowerCover (lowerChild p l) ∩ lowerCover (lowerChild p m)).Nonempty →
      lowerLocalLower p l ≤ trunkLocalUpper p m := by
    intro l m ⟨y, hy1, hy2⟩
    have h1' := Set.mem_Icc.mp hy1
    have h2' := Set.mem_Icc.mp hy2
    simp only [lowerLocalLower, trunkLocalUpper]
    by_cases hev : (lowerNormalize p).1.length % 2 = 0
    · simp only [hev, if_true]; linarith [h1'.1, h2'.2]
    · simp only [hev, if_false]; linarith [h1'.2, h2'.1]
  have sg : ∀ q : LowerPair, lowerStrictGood q → lowerGood q := by
    intro q h
    exact ⟨max (lowerEndpoint (lowerChild q ([1],[])) false)
               (lowerEndpoint (lowerChild q ([2],[])) false),
      ⟨le_max_left _ _, le_of_lt (lt_of_lt_of_le h (min_le_left _ _))⟩,
      ⟨le_max_right _ _, le_of_lt (lt_of_lt_of_le h (min_le_right _ _))⟩⟩
  -- ============ contacts and endpoints of the plan ============
  have hAB : (lowerCover (lowerChild p ([1],[])) ∩
      lowerCover (lowerChild p ([2],[1]))).Nonempty := by
    refine hTG.contacts ((([1],[]) : LowerLabel), (([2],[1]) : LowerLabel)) ?_ ?_ <;> simp
  have hCD : (lowerCover (lowerChild p ([2],[2])) ∩
      lowerCover (lowerChild p ([2],[3]))).Nonempty := by
    refine hTG.contacts ((([2],[2]) : LowerLabel), (([2],[3]) : LowerLabel)) ?_ ?_ <;> simp
  have hupper : lowerLocalCoordinate p t ≤ trunkLocalUpper p ([1],[]) :=
    le_trans hF2.2 (hTG.upper ([1],[]) (by simp))
  have hlower : lowerLocalLower p ([2],[3]) ≤ lowerLocalCoordinate p t :=
    le_trans (hTG.lower ([2],[3]) (by simp)) hF2.1
  have hgoodA : lowerGood (lowerChild p ([1],[])) := sg _ (hTG.strictGood _ (by simp))
  have hgoodB : lowerGood (lowerChild p ([2],[1])) := sg _ (hTG.strictGood _ (by simp))
  have hgoodD : lowerGood (lowerChild p ([2],[3])) := sg _ (hTG.strictGood _ (by simp))
  -- ============ offered labels ============
  have hoffA : lowerOffered p ([1],[]) := by
    refine Or.inl ?_
    rw [if_neg hc.1]
    unfold lowerEqualList
    split_ifs <;> simp
  have hoffB : lowerLStar p → lowerOffered p ([2],[1]) := by
    intro hLS
    refine Or.inl ?_
    rw [if_neg hc.1]
    unfold lowerEqualList
    rw [if_neg hc.2.1, if_neg hc.2.2.1, if_pos hLS]
    simp
  have hoffLate : ¬ lowerLStar p → ∀ l ∈ lowerLateList p, lowerOffered p l := by
    intro hLS l hl
    refine Or.inl ?_
    rw [if_neg hc.1]
    unfold lowerEqualList
    rw [if_neg hc.2.1, if_neg hc.2.2.1, if_neg hLS, if_pos hc.2.2.2]
    exact List.mem_append_left _ (List.mem_append_right _ hl)
  have hoffD : ¬ lowerLStar p → ¬ lowerRStar p → lowerOffered p ([2],[3]) := by
    intro hLS hRS
    refine Or.inl ?_
    rw [if_neg hc.1]
    unfold lowerEqualList
    rw [if_neg hc.2.1, if_neg hc.2.2.1, if_neg hLS, if_pos hc.2.2.2, if_neg hRS]
    simp
  -- ============ the walk ============
  have finish : ∀ (M : List LowerLabel), M ≠ [] →
      List.IsChain (fun l m => (lowerCover (lowerChild p l) ∩
        lowerCover (lowerChild p m)).Nonempty) ((([1],[]) : LowerLabel) :: M) →
      (∀ a ∈ (([1],[]) : LowerLabel) :: M,
        lowerOffered p a ∧ lowerGood (lowerChild p a)) →
      (∀ a, M.getLast? = some a → lowerLocalLower p a ≤ lowerLocalCoordinate p t) →
      lowerNumericSuccessor t p := by
    intro M hM hchain hall hlast
    obtain ⟨b0, t0, rfl⟩ : ∃ b0 t0, M = b0 :: t0 := by
      cases M with
      | nil => exact absurd rfl hM
      | cons b0 t0 => exact ⟨b0, t0, rfl⟩
    obtain ⟨a, ha, h1, h2⟩ := M7Last.walk (lowerLocalLower p) (trunkLocalUpper p) _
      hF4 (lowerLocalCoordinate p t) ((([1],[]) : LowerLabel) :: b0 :: t0) (by simp) hchain
      (fun a' ha' => by
        simp only [List.head?_cons, Option.some.injEq] at ha'
        exact ha' ▸ hupper)
      (fun a' ha' => hlast a' (by rwa [List.getLast?_cons_cons] at ha'))
    exact Or.inr ⟨a, (hall a ha).1, (hall a ha).2, hF1 a h1 h2⟩
  by_cases hLS : lowerLStar p
  · -- the `LStar` branch: the offered list is just the two top labels
    refine finish [([2],[1])] (by simp) ?_ ?_ ?_
    · exact List.isChain_cons_cons.mpr ⟨hAB, List.isChain_singleton _⟩
    · intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact ⟨hoffA, hgoodA⟩
      · exact ⟨hoffB hLS, hgoodB⟩
    · intro a ha
      simp only [List.getLast?_singleton, Option.some.injEq] at ha
      subst ha
      exact hb.1 hc.1 hc.2.1 hc.2.2.1 hLS
  · -- the generic branch: the late route bridges the hole of the plan
    have hex : ∃ ls, lowerLateRouteValid p ls :=
      hroute t p ⟨hadm, hgoodp, hcov, hbox⟩ ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2, hLS⟩ hlate
    have hlsv : lowerLateRouteValid p (lowerLateList p) := by
      have hchoice : lowerLateList p = Classical.choose hex := by
        unfold lowerLateList
        rw [dif_pos hex]
      rw [hchoice]
      exact Classical.choose_spec hex
    obtain ⟨hmemgood, hhead, hlast, hchain⟩ := hlsv
    have hne : lowerLateList p ≠ [] := by
      intro h; rw [h] at hhead; simp at hhead
    have hrevne : (lowerLateList p).reverse ≠ [] := by simpa using hne
    have hsymm : ∀ a b : LowerLabel,
        (lowerCover (lowerChild p a) ∩ lowerCover (lowerChild p b)).Nonempty →
        (lowerCover (lowerChild p b) ∩ lowerCover (lowerChild p a)).Nonempty := by
      intro a b h; rwa [Set.inter_comm] at h
    have hrev : List.IsChain (fun l m => (lowerCover (lowerChild p l) ∩
        lowerCover (lowerChild p m)).Nonempty) (lowerLateList p).reverse := by
      rw [List.isChain_reverse]
      exact hchain.imp (fun a b h => hsymm a b h)
    have hrevhead : (lowerLateList p).reverse.head? = some ([2],[1]) := by
      rw [List.head?_reverse]; exact hlast
    have hrevlast : (lowerLateList p).reverse.getLast? = some ([2],[2]) := by
      have := List.head?_reverse (l := (lowerLateList p).reverse)
      rw [List.reverse_reverse] at this
      rw [← this]; exact hhead
    have hallmid : ∀ a ∈ (lowerLateList p).reverse,
        lowerOffered p a ∧ lowerGood (lowerChild p a) := by
      intro a ha
      rw [List.mem_reverse] at ha
      exact ⟨hoffLate hLS a ha, (hmemgood a ha).2⟩
    by_cases hRS : lowerRStar p
    · refine finish (lowerLateList p).reverse hrevne ?_ ?_ ?_
      · refine List.isChain_cons.mpr ⟨?_, hrev⟩
        intro y hy
        rw [hrevhead] at hy
        simp only [Option.mem_def, Option.some.injEq] at hy
        exact hy ▸ hAB
      · intro a ha
        simp only [List.mem_cons] at ha
        rcases ha with rfl | ha
        · exact ⟨hoffA, hgoodA⟩
        · exact hallmid a ha
      · intro a ha
        rw [hrevlast] at ha
        simp only [Option.some.injEq] at ha
        subst ha
        exact hb.2.1 hc.1 hc.2.1 hRS
    · refine finish ((lowerLateList p).reverse ++ [([2],[3])]) (by simp) ?_ ?_ ?_
      · refine List.isChain_cons.mpr ⟨?_, ?_⟩
        · intro y hy
          have hh : ((lowerLateList p).reverse ++ [(([2],[3]) : LowerLabel)]).head?
              = some ([2],[1]) := by
            cases hcase : (lowerLateList p).reverse with
            | nil => exact absurd hcase hrevne
            | cons z zs =>
                rw [hcase] at hrevhead
                simp only [List.head?_cons, Option.some.injEq] at hrevhead
                simp [hrevhead]
          rw [hh] at hy
          simp only [Option.mem_def, Option.some.injEq] at hy
          subst hy
          exact hAB
        · refine List.isChain_append.mpr ⟨hrev, List.isChain_singleton _, ?_⟩
          intro x hx y hy
          rw [hrevlast] at hx
          simp only [Option.mem_def, Option.some.injEq] at hx
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
          exact hx ▸ hy ▸ hCD
      · intro a ha
        simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | ha | rfl
        · exact ⟨hoffA, hgoodA⟩
        · exact hallmid a ha
        · exact ⟨hoffD hLS hRS, hgoodD⟩
      · intro a ha
        rw [List.getLast?_append_of_ne_nil _ (by simp)] at ha
        simp only [List.getLast?_singleton, Option.some.injEq] at ha
        subst ha
        exact hlower
