-- Prove2me | solution 1 for Freiman.lowerHistory_earlier_anchor
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-13T13:56:26.753749+00:00
-- url     : https://prove2.me/submissions/b55cc51d-9ec6-4835-abb6-e7929dfdae48

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic
open Freiman
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem offered_23_cuts (p : LowerPair)
    (ho : lowerOffered p (([2],[3]) : LowerLabel)) :
    ¬ lowerA p 3 ∧ ¬ lowerA p 9 := by
  have heq : ¬ lowerMixed p ∧ (([2],[3]) : LowerLabel) ∈ lowerEqualList p := by
    unfold lowerOffered at ho
    rcases ho with ho | ho
    · by_cases hm : lowerMixed p
      · rw [if_pos hm] at ho
        unfold lowerMixedList at ho
        repeat' split_ifs at ho
        all_goals simp_all
      · rw [if_neg hm] at ho
        exact ⟨hm,ho⟩
    · rcases ho.2 with ⟨k,hk,he⟩
      have hleft := congrArg List.length (congrArg Prod.fst he)
      have hright := congrArg List.length (congrArg Prod.snd he)
      simp at hleft hright
      subst k
      norm_num at he
  constructor
  · intro h3
    have hm := heq.2
    simp [lowerEqualList, h3] at hm
  · intro h9
    have h3 : ¬ lowerA p 3 := by
      intro h3
      have hm := heq.2
      simp [lowerEqualList, h3] at hm
    have hm := heq.2
    simp [lowerEqualList, h3, h9] at hm
    unfold lowerEarlyList at hm
    repeat' split_ifs at hm
    all_goals simp_all

private theorem birth_length (p : LowerPair) (l : LowerLabel) (wide : Bool)
    (heq : lowerNormalize (lowerChild p l) = lowerHistoryOrient
      (lowerHistoryRawStep (lowerNormalize p) false (([2],[3]) : LowerLabel)) wide) :
    l.1.length + l.2.length = 2 := by
  have he := congrArg (fun z : LowerPair => z.1.length + z.2.length) heq
  unfold lowerChild lowerHistoryRawStep lowerHistoryOrient lowerNormalize at he
  repeat' split_ifs at he
  all_goals simp at he ⊢ <;> omega

private theorem normalize_parity (p : LowerPair)
    (hp : (lowerNormalize p).1.length % 2 = (lowerNormalize p).2.length % 2) :
    ¬ lowerMixed p := by
  unfold lowerMixed lowerNormalize at *
  split_ifs at hp <;> simp_all

private theorem offered_a3_length (p : LowerPair) (l : LowerLabel)
    (hm : ¬ lowerMixed p) (ho : lowerOffered p l) (h3 : lowerA p 3) :
    l.1.length + l.2.length ≠ 2 := by
  unfold lowerOffered at ho
  rw [if_neg hm] at ho
  rcases ho with ho | ho
  · simp [lowerEqualList,h3] at ho
    rcases ho with rfl | rfl | ⟨_,rfl⟩ <;> decide
  · exact fun _ => ho.1.2.1 h3

private theorem offered_a9_length (p : LowerPair) (l : LowerLabel)
    (hm : ¬ lowerMixed p) (ho : lowerOffered p l) (h3 : ¬lowerA p 3)
    (h9 : lowerA p 9) (hlen : l.1.length + l.2.length = 2) :
    (¬ lowerL p ∧ (l = (([3],[2]) : LowerLabel) ∨ l = (([2],[2]) : LowerLabel))) ∨
      l = (([3],[3]) : LowerLabel) := by
  unfold lowerOffered at ho
  rw [if_neg hm] at ho
  rcases ho with ho | ho
  · simp [lowerEqualList,h3,h9] at ho
    by_cases hL : lowerL p
    · simp [hL] at ho
      rcases ho with rfl | rfl <;> simp at hlen
    · left
      refine ⟨hL,?_⟩
      simp [hL] at ho
      repeat' split_ifs at ho
      all_goals
        simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
      all_goals
        try {rcases ho with rfl | rfl | rfl <;> simp at hlen ⊢}
      all_goals
        unfold lowerEarlyList at ho
        repeat' split_ifs at ho
        all_goals simp_all [List.mem_append]
        all_goals aesop
  · right
    rcases ho.2 with ⟨k,hk,rfl⟩
    simp at hlen
    have : k = 1 := by omega
    subst k
    rfl
private theorem c32_forces_left (p : LowerPair) (wide : Bool)
    (hr : lowerEnds (lowerNormalize p).2 [3,1])
    (heq : lowerNormalize (lowerChild p (([3],[2]) : LowerLabel)) =
      lowerHistoryOrient
        (lowerHistoryRawStep (lowerNormalize p) false (([2],[3]) : LowerLabel)) wide) :
    lowerL p := by
  let q := lowerNormalize p
  change lowerEnds q.2 [3,1] at hr
  change lowerEnds q.1 [3,1]
  change lowerNormalize (q.1++[3],q.2++[2]) =
    lowerHistoryOrient (q.1++[2],q.2++[3]) wide at heq
  unfold lowerNormalize at heq
  split_ifs at heq <;> cases wide <;>
    simp only [lowerHistoryOrient, if_false, if_true] at heq
  all_goals rcases Prod.mk.inj heq with ⟨h1,h2⟩
  · have hx := List.append_cancel_left h1
    norm_num at hx
  · have hx := List.append_cancel_right h1
    simpa [hx] using hr
  · have hx := List.append_cancel_right h1
    simpa [hx] using hr
  · have hx := List.append_cancel_left h1
    norm_num at hx

private theorem c22_impossible (p : LowerPair) (wide : Bool)
    (heq : lowerNormalize (lowerChild p (([2],[2]) : LowerLabel)) =
      lowerHistoryOrient
        (lowerHistoryRawStep (lowerNormalize p) false (([2],[3]) : LowerLabel)) wide) : False := by
  let q := lowerNormalize p
  change lowerNormalize (q.1++[2],q.2++[2]) =
    lowerHistoryOrient (q.1++[2],q.2++[3]) wide at heq
  unfold lowerNormalize at heq
  split_ifs at heq <;> cases wide <;>
    simp only [lowerHistoryOrient, if_false, if_true] at heq
  all_goals rcases Prod.mk.inj heq with ⟨h1,h2⟩
  · have hx := List.append_cancel_left h2
    norm_num at hx
  · have hx := List.append_cancel_left (h2.trans h1)
    norm_num at hx
  · have hx := List.append_cancel_left (h1.trans h2)
    norm_num at hx
  · have hx := List.append_cancel_left h1
    norm_num at hx

private theorem c33_impossible (p : LowerPair) (wide : Bool)
    (heq : lowerNormalize (lowerChild p (([3],[3]) : LowerLabel)) =
      lowerHistoryOrient
        (lowerHistoryRawStep (lowerNormalize p) false (([2],[3]) : LowerLabel)) wide) : False := by
  let q := lowerNormalize p
  change lowerNormalize (q.1++[3],q.2++[3]) =
    lowerHistoryOrient (q.1++[2],q.2++[3]) wide at heq
  unfold lowerNormalize at heq
  split_ifs at heq <;> cases wide <;>
    simp only [lowerHistoryOrient, if_false, if_true] at heq
  all_goals rcases Prod.mk.inj heq with ⟨h1,h2⟩
  · have hx := List.append_cancel_left h1
    norm_num at hx
  · have hx := List.append_cancel_left (h1.trans h2)
    norm_num at hx
  · have hx := List.append_cancel_left (h2.trans h1)
    norm_num at hx
  · have hx := List.append_cancel_left h2
    norm_num at hx

private theorem birth_cuts (p : LowerPair) (l : LowerLabel) (wide : Bool)
    (hpar : (lowerNormalize p).1.length % 2 = (lowerNormalize p).2.length % 2)
    (hr : lowerEnds (lowerNormalize p).2 [3,1])
    (ho : lowerOffered p l)
    (heq : lowerNormalize (lowerChild p l) = lowerHistoryOrient
      (lowerHistoryRawStep (lowerNormalize p) false (([2],[3]) : LowerLabel)) wide) :
    ¬ lowerA p 3 ∧ ¬ lowerA p 9 := by
  have hm := normalize_parity p hpar
  have hlen := birth_length p l wide heq
  have h3 : ¬ lowerA p 3 := by
    intro ha
    exact offered_a3_length p l hm ho ha hlen
  refine ⟨h3,?_⟩
  intro h9
  rcases offered_a9_length p l hm ho h3 h9 hlen with hc | hc
  · rcases hc with ⟨hnL,rfl | rfl⟩
    · exact hnL (c32_forces_left p wide hr heq)
    · exact c22_impossible p wide heq
  · subst l
    exact c33_impossible p wide heq

private theorem pe_append (u v : List ℕ+) (x : ℝ) :
    prefixEval (u ++ v) x = prefixEval u (prefixEval v x) := by
  induction u with
  | nil => rfl
  | cons a u ih => simp only [List.cons_append, prefixEval, ih]

private theorem pe_nonneg (w : List ℕ+) (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ prefixEval w x := by
  induction w with
  | nil => exact hx
  | cons a w ih =>
    simp only [prefixEval]
    exact div_nonneg zero_le_one (by positivity)

private theorem pe_mono_le (w : List ℕ+) (x y : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x ≤ y) :
    (w.length % 2 = 0 → prefixEval w x ≤ prefixEval w y) ∧
    (w.length % 2 = 1 → prefixEval w y ≤ prefixEval w x) := by
  induction w with
  | nil => exact ⟨fun _ => hxy, fun h => by simp at h⟩
  | cons a w ih =>
    have px := pe_nonneg w x hx
    have py := pe_nonneg w y hy
    constructor
    · intro he
      have ho : w.length % 2 = 1 := by simp at he; omega
      simp only [prefixEval]
      exact one_div_le_one_div_of_le (by positivity) (by linarith [ih.2 ho])
    · intro ho
      have he : w.length % 2 = 0 := by simp at ho; omega
      simp only [prefixEval]
      exact one_div_le_one_div_of_le (by positivity) (by linarith [ih.1 he])

private theorem tau_tail_le :
    prefixEval ([3,1,2,1,3] : List ℕ+) lowerTau ≤ prefixEval [3] lowerTau := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hn := Real.sqrt_nonneg (3 : ℝ)
  have ht : 0 < lowerTau := by unfold lowerTau; nlinarith
  have hA : 0 < (3 : ℝ) + lowerTau := by positivity
  have hB : 0 < (1 : ℝ) + 1 / ((3 : ℝ) + lowerTau) := by positivity
  have hC : 0 < (2 : ℝ) + 1 / ((1 : ℝ) + 1 / ((3 : ℝ) + lowerTau)) := by positivity
  have hD : 0 < (1 : ℝ) + 1 / ((2 : ℝ) + 1 / ((1 : ℝ) +
      1 / ((3 : ℝ) + lowerTau))) := by positivity
  simp only [prefixEval]
  apply one_div_le_one_div_of_le hA
  have htail : lowerTau ≤ 1 / ((1 : ℝ) + 1 / ((2 : ℝ) + 1 / ((1 : ℝ) +
      1 / ((3 : ℝ) + lowerTau)))) := by
    rw [le_div_iff₀ hD]
    field_simp [ne_of_gt hA, ne_of_gt hB, ne_of_gt hC]
    unfold lowerTau at *
    ring_nf at *
    nlinarith
  have hadd := add_le_add_right htail (3 : ℝ)
  norm_num [one_div, add_comm] at hadd ⊢
  exact hadd

private theorem tau_append_le_even (u : List ℕ+) (hu : u.length % 2 = 0) :
    prefixEval (u ++ [3,1,2,1,3]) lowerTau ≤ prefixEval (u ++ [3]) lowerTau := by
  rw [pe_append, pe_append]
  have ht : 0 ≤ lowerTau := by
    unfold lowerTau
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    have hn := Real.sqrt_nonneg (3 : ℝ)
    nlinarith
  apply (pe_mono_le u _ _ (pe_nonneg _ _ ht)
    (pe_nonneg _ _ ht) tau_tail_le).1 hu

private theorem tau_append_ge_odd (u : List ℕ+) (hu : u.length % 2 = 1) :
    prefixEval (u ++ [3]) lowerTau ≤ prefixEval (u ++ [3,1,2,1,3]) lowerTau := by
  rw [pe_append, pe_append]
  have ht : 0 ≤ lowerTau := by
    unfold lowerTau
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    have hn := Real.sqrt_nonneg (3 : ℝ)
    nlinarith
  apply (pe_mono_le u _ _ (pe_nonneg _ _ ht)
    (pe_nonneg _ _ ht) tau_tail_le).2 hu

private theorem equal_endpoint_natural (p : LowerPair) (upper : Bool)
    (hp : p.1.length % 2 = p.2.length % 2)
    (hn : lowerNaturalShort p.1 upper = true ∨ lowerNaturalShort p.2 upper = true) :
    lowerEndpoint p upper =
      4 + prefixEval (p.1 ++ lowerEndpointSuffix p.1 upper (lowerNaturalShort p.1 upper)) lowerTau +
        prefixEval (p.2 ++ lowerEndpointSuffix p.2 upper (lowerNaturalShort p.2 upper)) lowerTau := by
  rcases p with ⟨u,v⟩
  simp only [Prod.fst,Prod.snd] at hp hn ⊢
  unfold lowerEndpoint lowerEndpointWords
  simp only [hp,↓reduceIte]
  by_cases hw : lowerWidth v ≤ lowerWidth u
  · rcases hn with hn | hn <;> simp [lowerEqualWords,lowerNormalize,hw,hn]
  · rcases hn with hn | hn <;> simp [lowerEqualWords,lowerNormalize,hw,hn] <;> ring

private theorem suffix31 (u : List ℕ+) : lowerEnds (u++[3,1]) [3,1] :=
  List.suffix_append _ _
private theorem suffix3 (u : List ℕ+) : lowerEnds (u++[3]) [3] :=
  List.suffix_append _ _
private theorem not_suffix3_two (u : List ℕ+) : ¬ lowerEnds (u++[2]) [3] := by
  intro h; have := h.getLast (by simp); norm_num at this

private theorem parent_formula (u v : List ℕ+)
    (hp : u.length % 2 = v.length % 2)
    (hu : ¬ lowerEnds u [3,1]) (hv : lowerEnds v [3,1]) :
    if u.length % 2 = 0 then
      lowerEndpoint (u,v) false =
        4 + prefixEval (u++[3]) lowerTau + prefixEval (v++[2,1,3]) lowerTau
    else lowerEndpoint (u,v) true =
        4 + prefixEval (u++[3]) lowerTau + prefixEval (v++[2,1,3]) lowerTau := by
  by_cases he : u.length % 2 = 0
  · rw [if_pos he]
    have hv0 : v.length % 2 = 0 := by rw [← hp]; exact he
    have hs : lowerNaturalShort v false = true := by
      simp [lowerNaturalShort, hv0, hv]
    rw [equal_endpoint_natural _ false hp (Or.inr hs)]
    simp [lowerNaturalShort, lowerEndpointSuffix, he, hv0, hu, hv]
  · rw [if_neg he]
    have hu1 : u.length % 2 = 1 := by omega
    have hv1 : v.length % 2 = 1 := by rw [← hp]; exact hu1
    have hs : lowerNaturalShort v true = true := by
      simp [lowerNaturalShort, hv1, hv]
    rw [equal_endpoint_natural _ true hp (Or.inr hs)]
    simp [lowerNaturalShort, lowerEndpointSuffix, hu1, hv1, hu, hv]

private theorem child_lower_even_formula (u v : List ℕ+)
    (hu : u.length % 2 = 0) (hv : v.length % 2 = 0) :
    lowerEndpoint (u++[3],v++[2]) false =
      4 + prefixEval (u++[3,1,2,1,3]) lowerTau +
        prefixEval (v++[2,1,3]) lowerTau := by
  have hu1 : (u.length + 1) % 2 = 1 := by omega
  have hv1 : (v.length + 1) % 2 = 1 := by omega
  have hp : (u++[3]).length % 2 = (v++[2]).length % 2 := by
    simp only [List.length_append,List.length_singleton]; omega
  have hs : lowerNaturalShort (u++[3]) false = true := by
    simp [lowerNaturalShort, hu1, suffix3]
  rw [equal_endpoint_natural _ false hp (Or.inl hs)]
  simp [lowerNaturalShort, lowerEndpointSuffix, hu1, hv1, suffix3,
    not_suffix3_two, List.append_assoc]

private theorem child_upper_odd_formula (u v : List ℕ+)
    (hu : u.length % 2 = 1) (hv : v.length % 2 = 1) :
    lowerEndpoint (u++[3],v++[2]) true =
      4 + prefixEval (u++[3,1,2,1,3]) lowerTau +
        prefixEval (v++[2,1,3]) lowerTau := by
  have hu0 : (u.length + 1) % 2 = 0 := by omega
  have hv0 : (v.length + 1) % 2 = 0 := by omega
  have hp : (u++[3]).length % 2 = (v++[2]).length % 2 := by
    simp only [List.length_append,List.length_singleton]; omega
  have hs : lowerNaturalShort (u++[3]) true = true := by
    simp [lowerNaturalShort, hu0, suffix3]
  rw [equal_endpoint_natural _ true hp (Or.inl hs)]
  simp [lowerNaturalShort, lowerEndpointSuffix, hu0, hv0, suffix3,
    not_suffix3_two, List.append_assoc]

private theorem c32_alignment (u v : List ℕ+)
    (hp : u.length % 2 = v.length % 2)
    (hu : ¬ lowerEnds u [3,1]) (hv : lowerEnds v [3,1]) :
    if u.length % 2 = 0 then
      lowerEndpoint (u++[3],v++[2]) false ≤ lowerEndpoint (u,v) false
    else lowerEndpoint (u,v) true ≤ lowerEndpoint (u++[3],v++[2]) true := by
  have hparent := parent_formula u v hp hu hv
  by_cases he : u.length % 2 = 0
  · simp only [if_pos he] at hparent ⊢
    have hv0 : v.length % 2 = 0 := by rw [← hp]; exact he
    rw [child_lower_even_formula u v he hv0, hparent]
    linarith [tau_append_le_even u he]
  · simp only [if_neg he] at hparent ⊢
    have hu1 : u.length % 2 = 1 := by omega
    have hv1 : v.length % 2 = 1 := by rw [← hp]; exact hu1
    rw [child_upper_odd_formula u v hu1 hv1, hparent]
    linarith [tau_append_ge_odd u hu1]

private theorem normalize_idem_anchor (p : LowerPair) :
    lowerNormalize (lowerNormalize p) = lowerNormalize p := by
  unfold lowerNormalize
  split_ifs <;> simp_all
  all_goals exfalso; linarith

private theorem endpoint_normalize_equal_anchor (p : LowerPair) (u : Bool)
    (hp : p.1.length % 2 = p.2.length % 2) :
    lowerEndpoint (lowerNormalize p) u = lowerEndpoint p u := by
  unfold lowerEndpoint lowerEndpointWords
  rw [if_pos hp]
  have hpn : (lowerNormalize p).1.length % 2 = (lowerNormalize p).2.length % 2 := by
    unfold lowerNormalize; split_ifs <;> simp_all
  rw [if_pos hpn]
  unfold lowerEqualWords
  simp only [normalize_idem_anchor]
  have hw : lowerWidth (lowerNormalize p).2 ≤ lowerWidth (lowerNormalize p).1 := by
    unfold lowerNormalize; split_ifs with h
    · exact h
    · exact (not_le.mp h).le
  rw [if_pos hw]
  by_cases h : lowerWidth p.2 ≤ lowerWidth p.1
  · rw [if_pos h]
  · rw [if_neg h]; dsimp only [Prod.fst,Prod.snd]; ring

private theorem lstar_imp_l (p : LowerPair) : lowerLStar p → lowerL p := by
  intro h
  unfold lowerLStar lowerL lowerEnds at *
  exact (by decide : ([3,1] : List ℕ+).IsSuffix [3,1,3,1]).trans h

private theorem c21_impossible (p : LowerPair) (wide : Bool)
    (heq : lowerNormalize (lowerChild p (([2],[1]) : LowerLabel)) =
      lowerHistoryOrient
        (lowerHistoryRawStep (lowerNormalize p) false (([2],[3]) : LowerLabel)) wide) : False := by
  let q := lowerNormalize p
  change lowerNormalize (q.1++[2],q.2++[1]) =
    lowerHistoryOrient (q.1++[2],q.2++[3]) wide at heq
  unfold lowerNormalize at heq
  split_ifs at heq <;> cases wide <;>
    simp only [lowerHistoryOrient, if_false, if_true] at heq
  all_goals rcases Prod.mk.inj heq with ⟨h1,h2⟩
  · have hx := List.append_cancel_left h2; norm_num at hx
  · have hx := List.append_cancel_left (h2.trans h1); norm_num at hx
  · have hx := List.append_cancel_left (h1.trans h2); norm_num at hx
  · have hx := List.append_cancel_left h1; norm_num at hx

private theorem c31_impossible (p : LowerPair) (wide : Bool)
    (heq : lowerNormalize (lowerChild p (([3],[1]) : LowerLabel)) =
      lowerHistoryOrient
        (lowerHistoryRawStep (lowerNormalize p) false (([2],[3]) : LowerLabel)) wide) : False := by
  let q := lowerNormalize p
  change lowerNormalize (q.1++[3],q.2++[1]) =
    lowerHistoryOrient (q.1++[2],q.2++[3]) wide at heq
  unfold lowerNormalize at heq
  split_ifs at heq <;> cases wide <;>
    simp only [lowerHistoryOrient, if_false, if_true] at heq
  all_goals rcases Prod.mk.inj heq with ⟨h1,h2⟩
  · have hx := List.append_cancel_left h1; norm_num at hx
  · have hq := List.append_cancel_right h1
    rw [hq] at h2
    have hx := List.append_cancel_left h2; norm_num at hx
  · have hq := List.append_cancel_right h2
    rw [hq] at h1
    have hx := List.append_cancel_left h1; norm_num at hx
  · have hx := List.append_cancel_left h2; norm_num at hx

private theorem birth_selected_23 (p : LowerPair) (l : LowerLabel) (wide : Bool)
    (hpar : (lowerNormalize p).1.length % 2 = (lowerNormalize p).2.length % 2)
    (hr : lowerEnds (lowerNormalize p).2 [3,1])
    (hnL : ¬ lowerL p) (ho : lowerOffered p l)
    (heq : lowerNormalize (lowerChild p l) = lowerHistoryOrient
      (lowerHistoryRawStep (lowerNormalize p) false (([2],[3]) : LowerLabel)) wide) :
    l = (([2],[3]) : LowerLabel) := by
  have hm := normalize_parity p hpar
  have hc := birth_cuts p l wide hpar hr ho heq
  have hlen := birth_length p l wide heq
  have hnLS : ¬ lowerLStar p := fun h => hnL (lstar_imp_l p h)
  unfold lowerOffered at ho
  rw [if_neg hm] at ho
  rcases ho with ho | ho
  · simp [lowerEqualList, hc.1, hc.2, hnL, hnLS] at ho
    split_ifs at ho
    all_goals
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
    all_goals
      rcases ho with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp at hlen
    all_goals
      try {exact c32_forces_left p wide hr heq |> hnL.elim}
    all_goals
      try {exact (c22_impossible p wide heq).elim}
    all_goals
      try {exact (c21_impossible p wide heq).elim}
    all_goals
      try {exact (c31_impossible p wide heq).elim}
    all_goals rfl
  · rcases ho.2 with ⟨k,hk,rfl⟩
    simp at hlen
    have : k = 1 := by omega
    subst k
    exact (c33_impossible p wide heq).elim

 theorem solution (t : ℝ) (h : ℕ → LowerPair) (n : ℕ)
    (hh : lowerHistory t h n) (base : LowerPair) (p : LowerHistoryPath)
    (hp : lowerHistoryStructural p) (hr : lowerHistoryReached t h n base p)
    (hi : p.catalog ≠ .initial) : lowerHistoryEarlierAnchor base p t := by
  rcases hr with ⟨start,flip,hsum,hreal,hentry⟩
  rw [if_neg hi] at hentry
  unfold lowerHistoryRealizes at hreal
  simp only [hi,if_false] at hreal
  have hstart : 0 < start := hentry.1
  let m := start - 1
  have hm1 : m + 1 = start := by dsimp [m]; omega
  have hmn : m < n := by omega
  obtain ⟨l,ho,hpriority,hchild⟩ := hh.2.2 m hmn
  have hs := hh.2.1 m (by omega)
  have hpar : base.1.length % 2 = base.2.length % 2 := hreal.2.2.1
  have hnorm : lowerNormalize base = base := by
    rw [hentry.2.1]
    exact normalize_idem_anchor _
  have hparent : t ∈ lowerCover base := by
    have hrawpar : (h m).1.length % 2 = (h m).2.length % 2 := by
      change (h (start-1)).1.length % 2 = (h (start-1)).2.length % 2
      unfold lowerNormalize at hentry
      split_ifs at hentry <;> simp_all
    unfold lowerCover at hs ⊢
    change lowerEndpoint base false ≤ t ∧ t ≤ lowerEndpoint base true
    rw [hentry.2.1, endpoint_normalize_equal_anchor (h m) false hrawpar,
      endpoint_normalize_equal_anchor (h m) true hrawpar]
    exact hs.2.2.1
  have hctx := hreal.1
  have hright := hreal.2.1.1
  have heq : lowerNormalize (lowerChild (h m) l) = lowerHistoryOrient
      (lowerHistoryRawStep (lowerNormalize (h m)) false (([2],[3]) : LowerLabel))
      p.initialWider := by
    rw [← hchild, hm1]
    have hj := hreal.2.2.2 0 (by omega)
    simpa [lowerHistoryReplay,hentry.2.2.2,hentry.2.1] using hj.2.2
  by_cases hc : lowerEnds p.context [3,1]
  · have hc' : ([3,1] : List ℕ+).IsSuffix p.context := hc
    have hb31 : lowerEnds base.1 [3,1] := hctx.2.2.mpr hc
    by_cases he : base.1.length % 2 = 0
    · have hodd : decide (base.1.length % 2 = 1) = false := by simp; omega
      simpa [lowerHistoryEarlierAnchor, lowerHistoryEndpointReal,
        lowerHistoryAppend, lowerHistoryCommonOdd, hc', he, hodd] using hparent.1
    · have hodd : decide (base.1.length % 2 = 1) = true := by simp; omega
      simpa [lowerHistoryEarlierAnchor, lowerHistoryEndpointReal,
        lowerHistoryAppend, lowerHistoryCommonOdd, hc', he, hodd] using
          (neg_le_neg hparent.2)
  · have hc' : ¬ ([3,1] : List ℕ+).IsSuffix p.context := hc
    have hnL : ¬ lowerL (h m) := by
      unfold lowerL
      rw [← hentry.2.1]
      exact fun hb => hc (hctx.2.2.mp hb)
    have hpar' : (lowerNormalize (h m)).1.length % 2 =
        (lowerNormalize (h m)).2.length % 2 := by rw [← hentry.2.1]; exact hpar
    have hright' : lowerEnds (lowerNormalize (h m)).2 [3,1] := by
      rw [← hentry.2.1]
      exact hright
    have hl := birth_selected_23 (h m) l p.initialWider hpar' hright' hnL ho heq
    have hmixed := normalize_parity (h m) hpar'
    have hcuts := birth_cuts (h m) l p.initialWider hpar' hright' ho heq
    have hout : t ∉ lowerCover (lowerChild (h m) (([3],[2]) : LowerLabel)) := by
      exact hpriority.1 ⟨hmixed,hcuts.1,hcuts.2,hnL,hl⟩
    have hchild32 : lowerChild (h m) (([3],[2]) : LowerLabel) =
        (base.1++[3],base.2++[2]) := by
      simp [lowerChild,m,hentry.2.1,hnorm]
    rw [hchild32] at hout
    have halign := c32_alignment base.1 base.2 hpar (fun hb => hc (hctx.2.2.mp hb)) hright
    by_cases he : base.1.length % 2 = 0
    · have hodd : decide (base.1.length % 2 = 1) = false := by simp; omega
      have hlo : lowerEndpoint (base.1++[3],base.2++[2]) false ≤ t :=
        (show lowerEndpoint (base.1++[3],base.2++[2]) false ≤
            lowerEndpoint base false by simpa [he] using halign).trans hparent.1
      unfold lowerCover at hout
      simp only [Set.mem_Icc] at hout
      have hgoal := le_of_not_ge (fun h => hout ⟨hlo,h⟩)
      simpa [lowerHistoryEarlierAnchor, lowerHistoryEndpointReal,
        lowerHistoryAppend, lowerHistoryCommonOdd, hc', he, hodd] using hgoal
    · have hodd : decide (base.1.length % 2 = 1) = true := by simp; omega
      have hhi : t ≤ lowerEndpoint (base.1++[3],base.2++[2]) true :=
        hparent.2.trans (by simpa [he] using halign)
      unfold lowerCover at hout
      simp only [Set.mem_Icc] at hout
      have : t < lowerEndpoint (base.1++[3],base.2++[2]) false :=
        lt_of_not_ge (fun hlo => hout ⟨hlo,hhi⟩)
      have hgoal : -lowerEndpoint (base.1++[3],base.2++[2]) false ≤ -t := by
        linarith
      simpa [lowerHistoryEarlierAnchor, lowerHistoryEndpointReal,
        lowerHistoryAppend, lowerHistoryCommonOdd, hc', he, hodd] using hgoal

#print axioms solution
