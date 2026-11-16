-- Prove2me | solution 1 for CountOrderings.NFree.lemma_6_2
-- status  : ACCEPTED   (prove)
-- author  : @bersubs
-- created : 2026-11-15T17:28:58.783375+00:00
-- url     : https://prove2.me/submissions/8df6ad3d-485e-4f87-83f4-94ff99636c22

import Definitions.Def_CountOrderings_NFree_Reduction
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.Permutation
import Mathlib.Data.Nat.Factorial.BigOperators

open Finset
set_option autoImplicit false

namespace CountOrderings.NFree

private noncomputable def edgeOrders {α : Type*} [DecidableEq α]
    (s : Finset α) : Finset (List α) := s.toList.permutations.toFinset

private theorem mem_edgeOrders {α : Type*} [DecidableEq α] {s : Finset α} {l : List α} :
    l ∈ edgeOrders s ↔ l.Nodup ∧ l.toFinset = s := by
  simp only [edgeOrders, List.mem_toFinset, List.mem_permutations]
  constructor
  · intro h
    refine ⟨h.nodup_iff.mpr (Finset.nodup_toList _), ?_⟩
    ext a
    simpa using (h.mem_iff (a := a))
  · rintro ⟨hn, hs⟩
    apply (List.perm_ext_iff_of_nodup hn (Finset.nodup_toList _)).mpr
    intro a
    simpa using congrArg (fun t : Finset α => a ∈ t) hs

private theorem edgeOrders_cons_iff {α : Type*} [DecidableEq α]
    {s : Finset α} {a : α} {l : List α} :
    a :: l ∈ edgeOrders s ↔ a ∈ s ∧ l ∈ edgeOrders (s.erase a) := by
  simp only [mem_edgeOrders, List.nodup_cons, List.toFinset_cons]
  constructor
  · rintro ⟨⟨ha, hn⟩, he⟩
    refine ⟨?_, hn, ?_⟩
    · rw [← he]; simp
    · rw [← he, Finset.erase_insert]
      simp [ha]
  · rintro ⟨ha, hn, he⟩
    refine ⟨⟨?_, hn⟩, ?_⟩
    · intro hm
      exact (Finset.notMem_erase a s) (he ▸ List.mem_toFinset.mpr hm)
    · rw [he, Finset.insert_erase ha]

private theorem edgeOrders_empty {α : Type*} [DecidableEq α] :
    edgeOrders (∅ : Finset α) = {[]} := by
  ext l
  cases l <;> simp [mem_edgeOrders]

private theorem edgeOrders_eq_biUnion {α : Type*} [DecidableEq α]
    {s : Finset α} (hs : s.Nonempty) :
    edgeOrders s = s.biUnion (fun a => (edgeOrders (s.erase a)).image (List.cons a)) := by
  ext l
  cases l with
  | nil =>
    simp only [mem_edgeOrders, List.nodup_nil, List.toFinset_nil, true_and,
      Finset.mem_biUnion, Finset.mem_image, List.cons_ne_nil, and_false, exists_false]
    exact iff_false_intro (Ne.symm hs.ne_empty)
  | cons a l => simp [edgeOrders_cons_iff]

private def pathWeight {α : Type*} [DecidableEq α]
    (rate : Finset α → α → ℝ) (s : Finset α) : List α → ℝ
  | [] => 1
  | a :: l => rate s a * pathWeight rate (s.erase a) l

private theorem sum_pathWeight {α : Type*} [DecidableEq α]
    (rate : Finset α → α → ℝ)
    (hRate : ∀ s : Finset α, s.Nonempty → ∑ a ∈ s, rate s a = 1)
    (s : Finset α) : ∑ l ∈ edgeOrders s, pathWeight rate s l = 1 := by
  classical
  induction s using Finset.strongInduction with
  | H s ih =>
    by_cases hs : s.Nonempty
    · rw [edgeOrders_eq_biUnion hs, Finset.sum_biUnion]
      · calc
          _ = ∑ a ∈ s, rate s a := by
            apply Finset.sum_congr rfl
            intro a ha
            rw [Finset.sum_image (fun _ _ _ _ h => List.cons.inj h |>.2)]
            simp only [pathWeight]
            rw [← Finset.mul_sum, ih _ (Finset.erase_ssubset ha), mul_one]
          _ = 1 := hRate s hs
      · intro a _ b _ hab
        simp only [Function.onFun, Finset.disjoint_left]
        rintro _ hx hy
        obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨m, _, he⟩ := Finset.mem_image.mp hy
        exact hab (List.cons.inj he).1.symm
    · rw [Finset.not_nonempty_iff_eq_empty.mp hs, edgeOrders_empty]
      simp [pathWeight]

private theorem pathWeight_eq_prod {α : Type*} [DecidableEq α]
    (rate : Finset α → α → ℝ) (l : List α) (hl : l.Nodup) :
    pathWeight rate l.toFinset l =
      ∏ i : Fin l.length, rate (l.drop i.val).toFinset (l.get i) := by
  induction l with
  | nil => simp [pathWeight]
  | cons a l ih =>
    obtain ⟨ha, hn⟩ := List.nodup_cons.mp hl
    have herase : ((a :: l).toFinset).erase a = l.toFinset := by
      rw [List.toFinset_cons, Finset.erase_insert]
      simp [ha]
    rw [pathWeight, herase, ih hn]
    change _ = ∏ i : Fin (l.length + 1), rate ((a :: l).drop i.val).toFinset ((a :: l).get i)
    rw [Fin.prod_univ_succ]
    rfl

private def rootEdge (I : X3CInstance) (i : Fin I.n) : OrigEdge I :=
  ⟨.rootSet i, trivial⟩

private def edgeRoot {I : X3CInstance} (e : OrigEdge I) : OrigEdge I :=
  rootEdge I e.setIdx

private theorem rootEdge_idx (I : X3CInstance) (i : Fin I.n) :
    (rootEdge I i).setIdx = i := rfl

private theorem edgeRoot_idx {I : X3CInstance} (e : OrigEdge I) :
    (edgeRoot e).setIdx = e.setIdx := rfl

private theorem edgeRoot_root {I : X3CInstance} (e : OrigEdge I) :
    edgeRoot (edgeRoot e) = edgeRoot e := rfl

private theorem base_follows_iff {I : X3CInstance} (e f : OrigEdge I) :
    (baseDAG I).Follows e f ↔ e = edgeRoot f ∧ f ≠ edgeRoot f := by
  have eq_iff (a b : OrigEdge I) : (a = b) ↔ a.val = b.val :=
    ⟨congrArg Subtype.val, Subtype.ext⟩
  simp only [ne_eq, eq_iff]
  rcases e with ⟨e, he⟩
  rcases f with ⟨f, hf⟩
  cases e <;> cases f <;>
    simp [baseDAG, FinDigraph.Follows, OrigEdge.src, OrigEdge.tgt, edgeRoot, rootEdge,
      OrigEdge.setIdx]

private theorem mem_omegaLE_iff_root {I : X3CInstance} {σ : Fin (4 * I.n) ≃ OrigEdge I} :
    σ ∈ omegaLE I ↔ ∀ e : OrigEdge I, e ≠ edgeRoot e → σ.symm (edgeRoot e) < σ.symm e := by
  classical
  simp only [omegaLE, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h e he
    have hf := (base_follows_iff (edgeRoot e) e).mpr ⟨rfl, he⟩
    exact lt_of_le_of_ne (h _ _ (.single hf)) (fun h' => he (σ.symm.injective h').symm)
  · intro h e f hef
    induction hef with
    | refl => exact le_rfl
    | tail _ hf ih =>
      obtain ⟨rfl, hne⟩ := (base_follows_iff _ _).mp hf
      exact ih.trans (h _ hne).le

private noncomputable def edgeGroup (I : X3CInstance) (i : Fin I.n) : Finset (OrigEdge I) :=
  Finset.univ.filter (fun e => e.setIdx = i)

private theorem mem_edgeGroup {I : X3CInstance} {i : Fin I.n} {e : OrigEdge I} :
    e ∈ edgeGroup I i ↔ e.setIdx = i := by simp [edgeGroup]

private def edgeGroupEquiv (I : X3CInstance) (i : Fin I.n) :
    {e : OrigEdge I // e.setIdx = i} ≃ Option ↥(I.S i) where
  toFun
    | ⟨⟨.rootSet _, _⟩, _⟩ => none
    | ⟨⟨.setElem k j, h⟩, hk⟩ =>
      some ⟨j, show j ∈ I.S i from (show k = i from hk) ▸ h⟩
  invFun
    | none => ⟨rootEdge I i, rfl⟩
    | some j => ⟨⟨.setElem i j.val, j.property⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨e, he⟩, hi⟩
    cases e with
    | rootSet k => change k = i at hi; subst k; rfl
    | setElem k j => change k = i at hi; subst k; rfl
  right_inv := by rintro (_ | ⟨j, hj⟩) <;> rfl

private theorem card_edgeGroup (I : X3CInstance) (i : Fin I.n) : (edgeGroup I i).card = 4 := by
  classical
  rw [edgeGroup, ← Fintype.card_subtype, Fintype.card_congr (edgeGroupEquiv I i)]
  simp [I.card_S]

private theorem card_edgesOf (I : X3CInstance) (X : Finset (Fin I.n)) :
    (edgesOf I X).card = 4 * X.card := by
  classical
  have he : edgesOf I X = X.biUnion (edgeGroup I) := by
    ext e
    simp [edgesOf, mem_edgeGroup]
  rw [he, Finset.card_biUnion]
  · simp [card_edgeGroup, Nat.mul_comm]
  · intro i _ j _ hij
    refine Finset.disjoint_left.mpr (fun e hi hj => ?_)
    exact hij ((mem_edgeGroup.mp hi).symm.trans (mem_edgeGroup.mp hj))

private noncomputable def nonCoverEdges {I : X3CInstance} (X : Finset (Fin I.n))
    (s : Finset (OrigEdge I)) : Finset (OrigEdge I) :=
  s.filter (fun e => e.setIdx ∉ X)

private noncomputable def activeEdges {I : X3CInstance} (X : Finset (Fin I.n))
    (s : Finset (OrigEdge I)) : Finset (OrigEdge I) :=
  if (nonCoverEdges X s).Nonempty then nonCoverEdges X s else s

private theorem activeEdges_nonempty {I : X3CInstance} (X : Finset (Fin I.n))
    {s : Finset (OrigEdge I)} (hs : s.Nonempty) : (activeEdges X s).Nonempty := by
  unfold activeEdges
  split <;> assumption

private theorem activeEdges_subset {I : X3CInstance} (X : Finset (Fin I.n))
    (s : Finset (OrigEdge I)) : activeEdges X s ⊆ s := by
  unfold activeEdges
  split
  · exact Finset.filter_subset _ _
  · rfl

private theorem group_mem_active {I : X3CInstance} (X : Finset (Fin I.n))
    {s : Finset (OrigEdge I)} {e f : OrigEdge I}
    (he : e ∈ activeEdges X s) (hf : f ∈ s) (h : f.setIdx = e.setIdx) :
    f ∈ activeEdges X s := by
  classical
  unfold activeEdges at he ⊢
  split at he <;> rename_i hs
  · rw [if_pos hs]
    exact Finset.mem_filter.mpr ⟨hf, by
      rw [h]
      exact (Finset.mem_filter.mp he).2⟩
  · rw [if_neg hs]
    exact hf

private noncomputable def phaseBonus {I : X3CInstance} (X : Finset (Fin I.n))
    (s : Finset (OrigEdge I)) : ℝ :=
  if (nonCoverEdges X s).Nonempty then 0 else 1

private noncomputable def rawWeight {I : X3CInstance} (s : Finset (OrigEdge I))
    (bonus : ℝ) (e : OrigEdge I) : ℝ :=
  if e = edgeRoot e then 3 + bonus else if edgeRoot e ∈ s then 0 else 1

private noncomputable def stepWeight {I : X3CInstance} (X : Finset (Fin I.n))
    (s : Finset (OrigEdge I)) (e : OrigEdge I) : ℝ :=
  if e ∈ activeEdges X s then rawWeight (activeEdges X s) (phaseBonus X s) e else 0

private noncomputable def sumStepWeights {I : X3CInstance} (X : Finset (Fin I.n))
    (s : Finset (OrigEdge I)) : ℝ := ∑ e ∈ s, stepWeight X s e

private noncomputable def edgeRate {I : X3CInstance} (X : Finset (Fin I.n))
    (s : Finset (OrigEdge I)) (e : OrigEdge I) : ℝ :=
  stepWeight X s e / sumStepWeights X s

private theorem phaseBonus_nonneg {I : X3CInstance} (X : Finset (Fin I.n))
    (s : Finset (OrigEdge I)) : 0 ≤ phaseBonus X s := by
  unfold phaseBonus
  split <;> norm_num

private theorem stepWeight_nonneg {I : X3CInstance} (X : Finset (Fin I.n))
    (s : Finset (OrigEdge I)) (e : OrigEdge I) : 0 ≤ stepWeight X s e := by
  have hb := phaseBonus_nonneg X s
  unfold stepWeight rawWeight
  split
  · split
    · linarith
    · split <;> norm_num
  · norm_num

private theorem stepWeight_root_pos {I : X3CInstance} (X : Finset (Fin I.n))
    {s : Finset (OrigEdge I)} {e : OrigEdge I}
    (he : e ∈ activeEdges X s) (hr : e = edgeRoot e) :
    0 < stepWeight X s e := by
  have hb := phaseBonus_nonneg X s
  simp only [stepWeight, rawWeight, if_pos he, if_pos hr]
  linarith

private theorem sumStepWeights_pos {I : X3CInstance} (X : Finset (Fin I.n))
    {s : Finset (OrigEdge I)} (hs : s.Nonempty) : 0 < sumStepWeights X s := by
  classical
  have h := activeEdges_nonempty X hs
  obtain ⟨e, he⟩ := h
  have hex : ∃ e ∈ activeEdges X s, 0 < stepWeight X s e := by
    by_cases hr : e = edgeRoot e
    · exact ⟨e, he, stepWeight_root_pos X he hr⟩
    · by_cases hm : edgeRoot e ∈ activeEdges X s
      · exact ⟨edgeRoot e, hm, stepWeight_root_pos X hm (edgeRoot_root e).symm⟩
      · refine ⟨e, he, ?_⟩
        simp [stepWeight, rawWeight, he, hr, hm]
  obtain ⟨f, hf, hfpos⟩ := hex
  exact lt_of_lt_of_le hfpos
    (Finset.single_le_sum (fun a _ => stepWeight_nonneg X s a) (activeEdges_subset X s hf))

private theorem sum_edgeRate {I : X3CInstance} (X : Finset (Fin I.n))
    (s : Finset (OrigEdge I)) (hs : s.Nonempty) :
    ∑ e ∈ s, edgeRate X s e = 1 := by
  simp only [edgeRate, ← Finset.sum_div]
  exact div_self (sumStepWeights_pos X hs).ne' 

private theorem edgeRate_ne_zero_iff {I : X3CInstance} (X : Finset (Fin I.n))
    {s : Finset (OrigEdge I)} (hs : s.Nonempty) (e : OrigEdge I) :
    edgeRate X s e ≠ 0 ↔ e ∈ activeEdges X s ∧ (e = edgeRoot e ∨ edgeRoot e ∉ s) := by
  classical
  have hb : 3 + phaseBonus X s ≠ 0 := by linarith [phaseBonus_nonneg X s]
  have ht := (sumStepWeights_pos X hs).ne'
  by_cases he : e ∈ activeEdges X s
  · have hmem : edgeRoot e ∈ activeEdges X s ↔ edgeRoot e ∈ s :=
      ⟨fun h => activeEdges_subset X s h, fun h => group_mem_active X he h (edgeRoot_idx e)⟩
    rw [edgeRate, stepWeight, if_pos he, rawWeight]
    by_cases hroot : e = edgeRoot e
    · rw [if_pos hroot]
      exact iff_of_true (div_ne_zero hb ht) ⟨he, Or.inl hroot⟩
    · rw [if_neg hroot]
      by_cases hp : edgeRoot e ∈ s
      · have hp' := hmem.mpr hp
        simp [hp, hp', he, hroot]
      · have hp' := mt hmem.mp hp
        simp [hp, hp', he, hroot, ht]
  · simp [edgeRate, stepWeight, he]

private theorem sum_rawWeight_eq {I : X3CInstance} (s : Finset (OrigEdge I)) (b : ℝ)
    (hclosed : ∀ i : Fin I.n, rootEdge I i ∈ s → edgeGroup I i ⊆ s) :
    ∑ e ∈ s, rawWeight s b e = ∑ e ∈ s, if e = edgeRoot e then b else 1 := by
  classical
  rw [← Finset.sum_fiberwise s OrigEdge.setIdx, ← Finset.sum_fiberwise s OrigEdge.setIdx]
  apply Finset.sum_congr rfl
  intro i _
  let r := rootEdge I i
  let t := s.filter (fun e => e.setIdx = i)
  change (∑ e ∈ t, rawWeight s b e) = _
  have hroot (e : OrigEdge I) (he : e ∈ t) : edgeRoot e = r := by
    change rootEdge I e.setIdx = rootEdge I i
    rw [(Finset.mem_filter.mp he).2]
  by_cases hr : r ∈ s
  · have hrt : r ∈ t := Finset.mem_filter.mpr ⟨hr, rfl⟩
    have hgroup : t = edgeGroup I i := by
      ext e
      rw [mem_edgeGroup, Finset.mem_filter]
      exact ⟨And.right, fun h => ⟨hclosed i hr (mem_edgeGroup.mpr h), h⟩⟩
    have hcard : (t.erase r).card = 3 := by
      rw [Finset.card_erase_of_mem hrt, hgroup, card_edgeGroup]
    have hleft : (∑ e ∈ t, rawWeight s b e) = 3 + b := by
      rw [Finset.sum_eq_single_of_mem r hrt]
      · exact if_pos rfl
      · intro e he hne
        unfold rawWeight
        rw [hroot e he, if_neg hne, if_pos hr]
    rw [hleft, ← Finset.sum_erase_add _ _ hrt]
    have hsum : (∑ e ∈ t.erase r, if e = edgeRoot e then b else (1 : ℝ)) = 3 := by
      calc
        _ = ∑ _e ∈ t.erase r, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro e he
          rw [hroot e (Finset.mem_of_mem_erase he), if_neg (Finset.ne_of_mem_erase he)]
        _ = 3 := by simp [hcard]
    rw [hsum, if_pos (show r = edgeRoot r from rfl)]
  · apply Finset.sum_congr rfl
    intro e he
    have hne : e ≠ edgeRoot e := by
      intro h
      exact hr ((h.trans (hroot e he)) ▸ (Finset.mem_filter.mp he).1)
    unfold rawWeight
    rw [if_neg hne, if_neg hne, hroot e he, if_neg hr]

private theorem sumStepWeights_eq {I : X3CInstance} (X : Finset (Fin I.n))
    (s : Finset (OrigEdge I))
    (hclosed : ∀ i : Fin I.n, rootEdge I i ∈ s → edgeGroup I i ⊆ s) :
    sumStepWeights X s =
      ∑ e ∈ activeEdges X s, if e = edgeRoot e then phaseBonus X s else 1 := by
  classical
  have hclosed' : ∀ i : Fin I.n, rootEdge I i ∈ activeEdges X s → edgeGroup I i ⊆ activeEdges X s := by
    intro i hroot e he
    exact group_mem_active X hroot (hclosed i (activeEdges_subset X s hroot) he) (mem_edgeGroup.mp he)
  have hfilter : s.filter (fun e => e ∈ activeEdges X s) = activeEdges X s := by
    ext e
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun h => ⟨activeEdges_subset X s h, h⟩⟩
  rw [sumStepWeights]
  simp only [stepWeight, ← Finset.sum_filter, hfilter]
  exact sum_rawWeight_eq _ _ hclosed'

private def incidenceEdge (I : X3CInstance) (s : Fin I.n) (j : Fin (3 * I.h))
    (hsj : j ∈ I.S s) : OrigEdge I := ⟨.setElem s j, hsj⟩

private noncomputable def incomingPositions {I : X3CInstance}
    (σ : Fin (4 * I.n) ≃ OrigEdge I) (j : Fin (3 * I.h)) : Finset (Fin (4 * I.n)) := by
  classical
  exact Finset.univ.filter (fun p => ∃ s : Fin I.n, (σ p).1 = .setElem s j)

private theorem mem_incomingPositions {I : X3CInstance}
    (σ : Fin (4 * I.n) ≃ OrigEdge I) (j : Fin (3 * I.h)) (p : Fin (4 * I.n)) :
    p ∈ incomingPositions σ j ↔ ∃ s : Fin I.n, (σ p).1 = .setElem s j := by
  classical
  simp [incomingPositions]

private theorem incomingPositions_nonempty {I : X3CInstance} (hI : I.Standing)
    (σ : Fin (4 * I.n) ≃ OrigEdge I) (j : Fin (3 * I.h)) :
    (incomingPositions σ j).Nonempty := by
  obtain ⟨s, hsj⟩ := hI.1 j
  refine ⟨σ.symm (incidenceEdge I s j hsj), (mem_incomingPositions ..).mpr ⟨s, ?_⟩⟩
  rw [Equiv.apply_symm_apply]
  rfl

private noncomputable def lastPosition {I : X3CInstance} (hI : I.Standing)
    (σ : Fin (4 * I.n) ≃ OrigEdge I) (j : Fin (3 * I.h)) : Fin (4 * I.n) :=
  (incomingPositions σ j).max' (incomingPositions_nonempty hI σ j)

private theorem lastPosition_spec {I : X3CInstance} (hI : I.Standing)
    (σ : Fin (4 * I.n) ≃ OrigEdge I) (j : Fin (3 * I.h)) :
    ∃ s : Fin I.n, (σ (lastPosition hI σ j)).1 = .setElem s j :=
  (mem_incomingPositions ..).mp (Finset.max'_mem _ _)

private theorem le_lastPosition {I : X3CInstance} (hI : I.Standing)
    (σ : Fin (4 * I.n) ≃ OrigEdge I) (j : Fin (3 * I.h)) {p : Fin (4 * I.n)}
    (hp : ∃ s : Fin I.n, (σ p).1 = .setElem s j) : p ≤ lastPosition hI σ j :=
  Finset.le_max' _ _ ((mem_incomingPositions ..).mpr hp)

private theorem rho_eq_lastPosition {I : X3CInstance} (hI : I.Standing)
    (σ : Fin (4 * I.n) ≃ OrigEdge I) (j : Fin (3 * I.h)) :
    rho σ j = (lastPosition hI σ j).val + 1 := by
  change (incomingPositions σ j).sup (fun p => p.val + 1) = _
  apply le_antisymm
  · refine Finset.sup_le_iff.mpr fun p hp => Nat.succ_le_succ ?_
    exact le_lastPosition hI σ j ((mem_incomingPositions ..).mp hp)
  · exact Finset.le_sup (f := fun p : Fin (4 * I.n) => p.val + 1) (Finset.max'_mem _ _)


private def suffix (I : X3CInstance) (i : ℕ) : Finset (Fin (4 * I.n)) :=
  Finset.univ.filter (fun p => 4 * I.n ≤ p.val + i)

private theorem mem_suffix {I : X3CInstance} (i : ℕ) (p : Fin (4 * I.n)) :
    p ∈ suffix I i ↔ 4 * I.n ≤ p.val + i := by
  simp [suffix]

private theorem rootPosition_iff {I : X3CInstance}
    (σ : Fin (4 * I.n) ≃ OrigEdge I) (p : Fin (4 * I.n)) (s : Fin I.n) :
    p = σ.symm (rootEdge I s) ↔ (σ p).1 = .rootSet s := by
  constructor
  · rintro rfl
    rw [Equiv.apply_symm_apply]
    rfl
  · intro hp
    apply σ.injective
    rw [Equiv.apply_symm_apply]
    exact Subtype.ext hp


private noncomputable def suffixTargets {I : X3CInstance} (hI : I.Standing)
    (σ : Fin (4 * I.n) ≃ OrigEdge I) (i : ℕ) : Finset (Fin (3 * I.h)) := by
  classical
  exact Finset.univ.filter (fun j => lastPosition hI σ j ∈ suffix I i)

private def suffixRoots {I : X3CInstance}
    (σ : Fin (4 * I.n) ≃ OrigEdge I) (i : ℕ) : Finset (Fin I.n) :=
  Finset.univ.filter (fun s => σ.symm (rootEdge I s) ∈ suffix I i)

private theorem mem_suffixTargets {I : X3CInstance} (hI : I.Standing)
    (σ : Fin (4 * I.n) ≃ OrigEdge I) (i : ℕ) (j : Fin (3 * I.h)) :
    j ∈ suffixTargets hI σ i ↔ lastPosition hI σ j ∈ suffix I i := by
  classical
  simp [suffixTargets]

private theorem mem_suffixRoots {I : X3CInstance}
    (σ : Fin (4 * I.n) ≃ OrigEdge I) (i : ℕ) (s : Fin I.n) :
    s ∈ suffixRoots σ i ↔ σ.symm (rootEdge I s) ∈ suffix I i := by
  simp [suffixRoots]

private theorem Ccount_split {I : X3CInstance} (hI : I.Standing)
    (σ : Fin (4 * I.n) ≃ OrigEdge I) (i : ℕ) (hi : i ≤ 4 * I.n) :
    Ccount σ i = (suffixTargets hI σ i).card + (suffixRoots σ i).card := by
  classical
  unfold Ccount
  apply congrArg₂ (· + ·) <;> apply congrArg Finset.card
  · ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_suffixTargets,
      rho_eq_lastPosition hI, mem_suffix]
    omega
  · ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_suffixRoots,
      ← rootPosition_iff σ, mem_suffix]
    constructor
    · rintro ⟨p, hp, rfl⟩
      omega
    · intro hp
      exact ⟨_, by omega, rfl⟩


private theorem suffix_step {I : X3CInstance} (i : ℕ) (hi : i < 4 * I.n) :
    suffix I (i + 1) =
      insert (⟨4 * I.n - (i + 1), by omega⟩ : Fin (4 * I.n)) (suffix I i) := by
  ext p
  simp only [mem_suffix, Finset.mem_insert, Fin.ext_iff]
  omega

private theorem suffix_card {I : X3CInstance} (i : ℕ) (hi : i ≤ 4 * I.n) :
    (suffix I i).card = i := by
  induction i with
  | zero =>
    have he : suffix I 0 = ∅ := by
      ext p
      simp [mem_suffix, Nat.not_le_of_gt p.isLt]
    simp [he]
  | succ i ih =>
    rw [suffix_step i (by omega), Finset.card_insert_of_notMem, ih (by omega)]
    rw [mem_suffix]
    simp only
    omega


private theorem suffix_target_iff_exists {I : X3CInstance} (hI : I.Standing)
    (σ : Fin (4 * I.n) ≃ OrigEdge I) (i : ℕ) (j : Fin (3 * I.h)) :
    j ∈ suffixTargets hI σ i ↔
      ∃ p ∈ suffix I i, ∃ s : Fin I.n, (σ p).val = .setElem s j := by
  rw [mem_suffixTargets]
  constructor
  · intro hp
    exact ⟨lastPosition hI σ j, hp, lastPosition_spec hI σ j⟩
  · rintro ⟨p, hp, he⟩
    have hle : p.val ≤ (lastPosition hI σ j).val := le_lastPosition hI σ j he
    rw [mem_suffix] at hp ⊢
    omega


private theorem mem_edgesOf_iff {I : X3CInstance} {X : Finset (Fin I.n)}
    {e : OrigEdge I} : e ∈ edgesOf I X ↔ e.setIdx ∈ X := by
  classical
  simp [edgesOf]


private theorem omegaXC_iff_suffix {I : X3CInstance} (hI : I.Standing)
    (σ : Fin (4 * I.n) ≃ OrigEdge I) (X : Finset (Fin I.n)) :
    σ ∈ omegaXC I X ↔ σ ∈ omegaLE I ∧
      (suffix I (4 * I.h)).image σ = edgesOf I X := by
  classical
  have he : ((Finset.univ : Finset (Fin (4 * I.n))).filter
      (fun p => 4 * I.n - 4 * I.h ≤ p.val)) = suffix I (4 * I.h) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_suffix]
    have hhn := hI.2
    omega
  rw [omegaXC, Finset.mem_filter, he]


private def remaining {I : X3CInstance}
    (σ : Fin (4 * I.n) ≃ OrigEdge I) (i : ℕ) : Finset (OrigEdge I) :=
  (suffix I i).map σ.toEmbedding

private theorem mem_remaining {I : X3CInstance}
    (σ : Fin (4 * I.n) ≃ OrigEdge I) (i : ℕ) (e : OrigEdge I) :
    e ∈ remaining σ i ↔ 4 * I.n ≤ (σ.symm e).val + i := by
  rw [remaining, Finset.mem_map_equiv, mem_suffix]

private theorem card_remaining {I : X3CInstance}
    (σ : Fin (4 * I.n) ≃ OrigEdge I) (i : ℕ) (hi : i ≤ 4 * I.n) :
    (remaining σ i).card = i := by
  rw [remaining, Finset.card_map, suffix_card i hi]

private theorem remaining_mono {I : X3CInstance} (σ : Fin (4 * I.n) ≃ OrigEdge I)
    {i j : ℕ} (hij : i ≤ j) : remaining σ i ⊆ remaining σ j := by
  intro e he
  rw [mem_remaining] at he ⊢
  omega

private theorem remaining_cover_eq {I : X3CInstance} (hI : I.Standing)
    (σ : Fin (4 * I.n) ≃ OrigEdge I) {X : Finset (Fin I.n)} (hσX : σ ∈ omegaXC I X) :
    remaining σ (4 * I.h) = edgesOf I X := by
  rw [remaining, Finset.map_eq_image]
  exact ((omegaXC_iff_suffix hI σ X).mp hσX).2

private theorem remaining_closed {I : X3CInstance} {σ : Fin (4 * I.n) ≃ OrigEdge I}
    (hσ : σ ∈ omegaLE I) (i : ℕ) :
    ∀ k : Fin I.n, rootEdge I k ∈ remaining σ i → edgeGroup I k ⊆ remaining σ i := by
  intro k hk e he
  have hidx := mem_edgeGroup.mp he
  have hr : edgeRoot e = rootEdge I k := congrArg (rootEdge I) hidx
  by_cases h : e = edgeRoot e
  · rwa [h, hr]
  · have hlt := (mem_omegaLE_iff_root.mp hσ) e h
    rw [hr] at hlt
    have hle : (σ.symm (rootEdge I k)).val ≤ (σ.symm e).val := hlt.le
    rw [mem_remaining] at hk ⊢
    omega

private theorem nonCoverEdges_eq_sdiff {I : X3CInstance} (X : Finset (Fin I.n))
    (s : Finset (OrigEdge I)) :
    nonCoverEdges X s = s \ edgesOf I X := by
  classical
  ext e
  simp only [nonCoverEdges, Finset.mem_filter, Finset.mem_sdiff, mem_edgesOf_iff]

private theorem nonCoverEdges_remaining_nonempty_iff {I : X3CInstance} (hI : I.Standing)
    (σ : Fin (4 * I.n) ≃ OrigEdge I) {X : Finset (Fin I.n)} (hX : I.IsExactCover X)
    (hσX : σ ∈ omegaXC I X) (i : ℕ) (hi : i ≤ 4 * I.n) :
    (nonCoverEdges X (remaining σ i)).Nonempty ↔ 4 * I.h < i := by
  rw [nonCoverEdges_eq_sdiff]
  constructor
  · intro h
    by_contra! hle
    exact (Finset.sdiff_nonempty.mp h)
      ((remaining_cover_eq hI σ hσX) ▸ remaining_mono σ hle)
  · intro h
    apply Finset.sdiff_nonempty_of_card_lt_card
    rw [card_remaining σ i hi, card_edgesOf I X, hX.1]
    exact h

private def rootLabels {I : X3CInstance} (s : Finset (OrigEdge I)) : Finset (Fin I.n) :=
  Finset.univ.filter (fun j => rootEdge I j ∈ s)

private theorem card_rootLabels {I : X3CInstance} (s : Finset (OrigEdge I)) :
    (s.filter (fun e => e = edgeRoot e)).card = (rootLabels s).card := by
  classical
  let f : Fin I.n ↪ OrigEdge I := ⟨rootEdge I, fun _ _ he => congrArg OrigEdge.setIdx he⟩
  rw [← Finset.card_map (f := f)]
  apply congrArg Finset.card
  ext e
  simp only [Finset.mem_filter, Finset.mem_map, rootLabels, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨he, hr⟩
    exact ⟨e.setIdx, hr ▸ he, hr.symm⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨hj, rfl⟩

private theorem sum_nonroot {I : X3CInstance} (s : Finset (OrigEdge I)) :
    (∑ e ∈ s, if e = edgeRoot e then (0 : ℝ) else 1) =
      (s.card : ℝ) - ((rootLabels s).card : ℝ) := by
  classical
  have hroot : (∑ e ∈ s, if e = edgeRoot e then (1 : ℝ) else 0) =
      ((rootLabels s).card : ℝ) := by
    rw [← Finset.sum_filter, ← card_rootLabels s]
    simp
  calc
    _ = ∑ e ∈ s, (1 - (if e = edgeRoot e then (1 : ℝ) else 0)) := by
      apply Finset.sum_congr rfl
      intro e _
      by_cases hr : e = edgeRoot e
      · simp only [if_pos hr, sub_self]
      · simp only [if_neg hr, sub_zero]
    _ = _ := by rw [Finset.sum_sub_distrib, hroot]; simp

private theorem rootLabels_remaining {I : X3CInstance}
    (σ : Fin (4 * I.n) ≃ OrigEdge I) (i : ℕ) :
    rootLabels (remaining σ i) = suffixRoots σ i := by
  ext s
  simp only [rootLabels, Finset.mem_filter, Finset.mem_univ, true_and, mem_remaining,
    mem_suffixRoots, mem_suffix]

private theorem rootLabels_edgesOf {I : X3CInstance} (X : Finset (Fin I.n)) :
    rootLabels (edgesOf I X) = X := by
  ext s
  simp only [rootLabels, Finset.mem_filter, Finset.mem_univ, true_and, mem_edgesOf_iff, rootEdge_idx]

private theorem suffixTargets_above_cover {I : X3CInstance} (hI : I.Standing)
    (σ : Fin (4 * I.n) ≃ OrigEdge I) {X : Finset (Fin I.n)} (hX : I.IsExactCover X)
    (hσX : σ ∈ omegaXC I X) {i : ℕ} (hi : 4 * I.h ≤ i) :
    suffixTargets hI σ i = Finset.univ := by
  apply Finset.eq_univ_iff_forall.mpr
  intro j
  have hj : j ∈ X.biUnion I.S := hX.2.symm ▸ Finset.mem_univ j
  obtain ⟨s, hs, hsj⟩ := Finset.mem_biUnion.mp hj
  let e := incidenceEdge I s j hsj
  have he : e ∈ edgesOf I X := mem_edgesOf_iff.mpr hs
  rw [← remaining_cover_eq hI σ hσX] at he
  have hp := (mem_remaining σ i e).mp (remaining_mono σ hi he)
  apply (suffix_target_iff_exists hI σ i j).mpr
  refine ⟨σ.symm e, (mem_suffix ..).mpr hp, s, ?_⟩
  rw [Equiv.apply_symm_apply]
  rfl

private theorem sumStepWeights_remaining {I : X3CInstance} (hI : I.Standing)
    (σ : Fin (4 * I.n) ≃ OrigEdge I) {X : Finset (Fin I.n)} (hX : I.IsExactCover X)
    (hσX : σ ∈ omegaXC I X) (i : ℕ) (hi : i ≤ 4 * I.n) :
    sumStepWeights X (remaining σ i) =
      if i ≤ 4 * I.h then (i : ℝ) else (i : ℝ) - Ccount σ i := by
  classical
  have hσ := ((omegaXC_iff_suffix hI σ X).mp hσX).1
  have hphase := nonCoverEdges_remaining_nonempty_iff hI σ hX hσX i hi
  rw [sumStepWeights_eq X _ (remaining_closed hσ i)]
  by_cases hle : i ≤ 4 * I.h
  · have hn : ¬ (nonCoverEdges X (remaining σ i)).Nonempty := fun he =>
      (not_lt_of_ge hle) (hphase.mp he)
    simp only [if_pos hle, activeEdges, phaseBonus, if_neg hn, ite_self, Finset.sum_const,
      nsmul_eq_mul, mul_one, card_remaining σ i hi]
  · have hLarge : 4 * I.h < i := Nat.lt_of_not_ge hle
    have hn : (nonCoverEdges X (remaining σ i)).Nonempty := hphase.mpr hLarge
    have hsub : edgesOf I X ⊆ remaining σ i := by
      rw [← remaining_cover_eq hI σ hσX]
      exact remaining_mono σ hLarge.le
    have hsum := Finset.sum_sdiff (f := fun e : OrigEdge I =>
      if e = edgeRoot e then (0 : ℝ) else 1) hsub
    rw [← nonCoverEdges_eq_sdiff, sum_nonroot (edgesOf I X), sum_nonroot (remaining σ i),
      card_edgesOf, card_remaining σ i hi, rootLabels_edgesOf, rootLabels_remaining, hX.1] at hsum
    have hcount := Ccount_split hI σ i hi
    rw [suffixTargets_above_cover hI σ hX hσX hLarge.le, Finset.card_univ, Fintype.card_fin] at hcount
    simp only [if_neg hle, activeEdges, phaseBonus, if_pos hn]
    have hcountReal : (Ccount σ i : ℝ) = 3 * (I.h : ℝ) +
        ((suffixRoots σ i).card : ℝ) := by exact_mod_cast hcount
    push_cast at hsum
    linarith


private noncomputable def rootMultiplier {I : X3CInstance} (X : Finset (Fin I.n))
    (e : OrigEdge I) : ℝ :=
  if e = edgeRoot e then if e.setIdx ∈ X then 4 else 3 else 1

private theorem prod_rootMultiplier {I : X3CInstance} (X : Finset (Fin I.n)) :
    ∏ e : OrigEdge I, rootMultiplier X e = (4 : ℝ)^X.card * (3 : ℝ)^(I.n - X.card) := by
  classical
  let incl : Fin I.n ↪ OrigEdge I :=
    ⟨rootEdge I, fun _ _ he => congrArg OrigEdge.setIdx he⟩
  have hprod :
      (∏ e ∈ Finset.univ.map incl, rootMultiplier X e) =
        ∏ e : OrigEdge I, rootMultiplier X e := by
    apply Finset.prod_subset (Finset.subset_univ _)
    intro e _ he
    have hr : e ≠ edgeRoot e := by
      intro hr
      apply he
      exact Finset.mem_map.mpr ⟨e.setIdx, Finset.mem_univ _, hr.symm⟩
    exact if_neg hr
  rw [← hprod, Finset.prod_map]
  have hr (j : Fin I.n) : rootMultiplier X (incl j) = if j ∈ X then 4 else 3 := by
    unfold rootMultiplier
    rw [if_pos (show incl j = edgeRoot (incl j) from rfl)]
    rfl
  simp_rw [hr]
  rw [Finset.prod_ite]
  have hx : (Finset.univ : Finset (Fin I.n)).filter (fun j => j ∈ X) = X := by
    ext j
    simp
  have hxc : (Finset.univ : Finset (Fin I.n)).filter (fun j => j ∉ X) =
      Finset.univ \ X := by
    ext j
    simp
  rw [hx, hxc, Finset.prod_const, Finset.prod_const,
    Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  simp

private theorem prod_by_reverse_positions (m : ℕ) (f : ℕ → ℝ) :
    ∏ p : Fin m, f (m - p.val) = ∏ i ∈ Finset.Icc 1 m, f i := by
  refine Finset.prod_bij (fun p _ => m - p.val) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro p _
    have hp := p.isLt
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro p _ q _ h
    have hp := p.isLt
    have hq := q.isLt
    apply Fin.ext
    omega
  · intro i hi
    obtain ⟨hi, him⟩ := Finset.mem_Icc.mp hi
    exact ⟨⟨m-i, by omega⟩, Finset.mem_univ _, by simp; omega⟩

private theorem prod_Icc_real_factorial (m : ℕ) :
    ∏ i ∈ Finset.Icc 1 m, (i : ℝ) = (m.factorial : ℝ) := by
  rw [← Finset.prod_range_add_one_eq_factorial m, Nat.cast_prod]
  symm
  refine Finset.prod_bij (fun i _ => i+1) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro i hi
    have hi := Finset.mem_range.mp hi
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro i _ j _ h
    omega
  · intro i hi
    obtain ⟨hi, him⟩ := Finset.mem_Icc.mp hi
    exact ⟨i-1, Finset.mem_range.mpr (by omega), by omega⟩

private theorem prod_split_suffix {h n : ℕ} (hhn : h ≤ n) (C : ℕ → ℕ) :
    (∏ i ∈ Finset.Icc 1 (4 * n), 1 / (if i ≤ 4*h then (i : ℝ) else (i : ℝ) - C i)) =
      (∏ i ∈ Finset.Icc (4*h+1) (4*n), 1 / ((i : ℝ) - C i)) / ((4*h).factorial : ℝ) := by
  have hj : Finset.Icc 1 (4*h) ∪ Finset.Icc (4*h+1) (4*n) = Finset.Icc 1 (4*n) := by
    ext i
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  have hd : Disjoint (Finset.Icc 1 (4*h)) (Finset.Icc (4*h+1) (4*n)) := by
    rw [Finset.disjoint_left]
    intro i hi hj
    have h1 := (Finset.mem_Icc.mp hi).2
    have h2 := (Finset.mem_Icc.mp hj).1
    omega
  rw [← hj, Finset.prod_union hd]
  have hsmall :
      (∏ i ∈ Finset.Icc 1 (4*h), 1 / (if i ≤ 4*h then (i : ℝ) else (i : ℝ) - C i)) =
        1 / ((4*h).factorial : ℝ) := by
    calc
      _ = ∏ i ∈ Finset.Icc 1 (4*h), 1 / (i : ℝ) := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [if_pos (Finset.mem_Icc.mp hi).2]
      _ = _ := by rw [Finset.prod_div_distrib, prod_Icc_real_factorial, Finset.prod_const_one]
  have hlarge :
      (∏ i ∈ Finset.Icc (4*h+1) (4*n), 1 / (if i ≤ 4*h then (i : ℝ) else (i : ℝ) - C i)) =
        ∏ i ∈ Finset.Icc (4*h+1) (4*n), 1 / ((i : ℝ) - C i) := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [if_neg (by have := (Finset.mem_Icc.mp hi).1; omega)]
  rw [hsmall, hlarge]
  ring



private theorem orderingList_toFinset {I : X3CInstance} (σ : Fin (4 * I.n) ≃ OrigEdge I) :
    (List.ofFn σ).toFinset = Finset.univ := by
  ext e
  exact iff_of_true (List.mem_toFinset.mpr (List.mem_ofFn.mpr
    ⟨σ.symm e, σ.apply_symm_apply e⟩)) (Finset.mem_univ e)

private theorem edgeOrders_univ_image (I : X3CInstance) :
    edgeOrders (Finset.univ : Finset (OrigEdge I)) =
      Finset.univ.image (fun σ : Fin (4 * I.n) ≃ OrigEdge I => List.ofFn σ) := by
  classical
  have hEdges : edgesOf I (Finset.univ : Finset (Fin I.n)) = Finset.univ := by
    apply Finset.ext
    intro e
    simp [edgesOf]
  have hCard : (Finset.univ : Finset (OrigEdge I)).card = 4 * I.n := by
    rw [← hEdges, card_edgesOf]
    simp
  apply Finset.ext
  intro l
  rw [mem_edgeOrders, Finset.mem_image]
  constructor
  · rintro ⟨hNodup, hF⟩
    have hFull (e : OrigEdge I) : e ∈ l :=
      List.mem_toFinset.mp (hF ▸ Finset.mem_univ e)
    have hLen : l.length = 4 * I.n := by
      rw [← List.toFinset_card_of_nodup hNodup, hF, hCard]
    let σ := (finCongr hLen.symm).trans (List.Nodup.getEquivOfForallMemList l hNodup hFull)
    refine ⟨σ, Finset.mem_univ σ, ?_⟩
    apply List.ext_getElem
    · simpa using hLen.symm
    · intro i hi hj
      rw [List.getElem_ofFn]
      rfl
  · rintro ⟨σ, _, rfl⟩
    exact ⟨List.nodup_ofFn_ofInjective σ.injective, orderingList_toFinset σ⟩

private theorem drop_orderingList_toFinset {I : X3CInstance}
    (σ : Fin (4 * I.n) ≃ OrigEdge I) (p : ℕ) (hp : p ≤ 4 * I.n) :
    ((List.ofFn σ).drop p).toFinset = remaining σ (4 * I.n - p) := by
  apply Finset.ext
  intro e
  rw [List.mem_toFinset, List.mem_iff_getElem, mem_remaining]
  constructor
  · rintro ⟨j, hj, he⟩
    rw [List.getElem_drop, List.getElem_ofFn] at he
    have hIndex := congrArg (fun e' : OrigEdge I => (σ.symm e').val) he
    simp only [Equiv.symm_apply_apply] at hIndex
    change p + j = (σ.symm e).val at hIndex
    omega
  · intro he
    let j := (σ.symm e).val - p
    have hIndex : p + j = (σ.symm e).val := by dsimp [j]; omega
    have hj : j < ((List.ofFn σ).drop p).length := by
      simp only [List.length_drop, List.length_ofFn]
      have := (σ.symm e).isLt
      omega
    refine ⟨j, hj, ?_⟩
    rw [List.getElem_drop, List.getElem_ofFn]
    exact (congrArg σ (Fin.ext hIndex)).trans (Equiv.apply_symm_apply σ e)

private theorem pathWeight_orderingList {I : X3CInstance} (X : Finset (Fin I.n))
    (σ : Fin (4 * I.n) ≃ OrigEdge I) :
    pathWeight (edgeRate X) Finset.univ (List.ofFn σ) =
      ∏ p : Fin (4 * I.n), edgeRate X (remaining σ (4 * I.n - p.val)) (σ p) := by
  rw [← orderingList_toFinset σ,
    pathWeight_eq_prod _ _ (List.nodup_ofFn_ofInjective σ.injective)]
  refine Fintype.prod_equiv (finCongr List.length_ofFn) _ _ fun p => ?_
  rw [List.get_ofFn, drop_orderingList_toFinset]
  · rfl
  · exact (p.isLt.trans_eq List.length_ofFn).le

private theorem mem_omegaXC_of_nonzero_pathRates {I : X3CInstance} (hI : I.Standing)
    (X : Finset (Fin I.n)) (hX : X ∈ I.exactCovers) (σ : Fin (4 * I.n) ≃ OrigEdge I)
    (hRate : ∀ p : Fin (4 * I.n),
      edgeRate X (remaining σ (4 * I.n - p.val)) (σ p) ≠ 0) :
    σ ∈ omegaXC I X := by
  classical
  have hStep (e : OrigEdge I) :
      e ∈ activeEdges X (remaining σ (4 * I.n - (σ.symm e).val)) ∧
      (e = edgeRoot e ∨ edgeRoot e ∉ remaining σ (4 * I.n - (σ.symm e).val)) := by
    have hm : e ∈ remaining σ (4 * I.n - (σ.symm e).val) := by
      rw [mem_remaining]
      omega
    apply (edgeRate_ne_zero_iff X ⟨e, hm⟩ e).mp
    simpa only [Equiv.apply_symm_apply] using hRate (σ.symm e)
  have hLE : σ ∈ omegaLE I := by
    apply mem_omegaLE_iff_root.mpr
    intro e hne
    have hBefore := or_iff_not_imp_left.mp (hStep e).2 hne
    rw [mem_remaining] at hBefore
    change (σ.symm (edgeRoot e)).val < (σ.symm e).val
    omega
  have hOrdered (e f : OrigEdge I) (he : e.setIdx ∈ X) (hf : f.setIdx ∉ X) :
      (σ.symm f).val < (σ.symm e).val := by
    by_contra! h
    have hfR : f ∈ remaining σ (4 * I.n - (σ.symm e).val) := by
      rw [mem_remaining]
      omega
    have hNoncover : (nonCoverEdges X (remaining σ (4 * I.n - (σ.symm e).val))).Nonempty :=
      ⟨f, Finset.mem_filter.mpr ⟨hfR, hf⟩⟩
    have hActive := (hStep e).1
    rw [activeEdges, if_pos hNoncover] at hActive
    exact (Finset.mem_filter.mp hActive).2 he
  have hh := hI.2
  have hXcard : X.card = I.h := (Finset.mem_filter.mp hX).2.1
  have hEqualCard : (remaining σ (4 * I.h)).card = (edgesOf I X).card := by
    rw [card_remaining σ _ (by omega), card_edgesOf, hXcard]
  have hSuffix : remaining σ (4 * I.h) = edgesOf I X := by
    refine Finset.eq_of_subset_of_card_le (fun f hf => ?_) hEqualCard.ge
    by_contra hNot
    have hCoverSubset : edgesOf I X ⊆ remaining σ (4 * I.h) := by
      intro e he
      have hePos := hOrdered e f (mem_edgesOf_iff.mp he) (fun hx => hNot (mem_edgesOf_iff.mpr hx))
      rw [mem_remaining] at hf ⊢
      omega
    have hEq := Finset.eq_of_subset_of_card_le hCoverSubset hEqualCard.le
    rw [← hEq] at hf
    exact hNot hf
  refine (omegaXC_iff_suffix hI σ X).mpr ⟨hLE, ?_⟩
  rw [remaining, Finset.map_eq_image] at hSuffix
  exact hSuffix

private theorem sum_omegaXC_pathRates (I : X3CInstance) (hI : I.Standing)
    (X : Finset (Fin I.n)) (hX : X ∈ I.exactCovers) :
    ∑ σ ∈ omegaXC I X, ∏ p : Fin (4 * I.n),
      edgeRate X (remaining σ (4 * I.n - p.val)) (σ p) = 1 := by
  classical
  have hTotal := sum_pathWeight (edgeRate X) (sum_edgeRate X) Finset.univ
  rw [edgeOrders_univ_image I, Finset.sum_image] at hTotal
  · simp only [pathWeight_orderingList] at hTotal
    refine (Finset.sum_subset (Finset.subset_univ _) fun σ _ hn => ?_).trans hTotal
    by_contra h
    refine hn (mem_omegaXC_of_nonzero_pathRates hI X hX σ fun p => ?_)
    exact Finset.prod_ne_zero_iff.mp h p (Finset.mem_univ p)
  · intro σ _ τ _ he
    exact Equiv.ext (congrFun (List.ofFn_inj.mp he))


private theorem weight_num_eq_multiplier {I : X3CInstance} (hI : I.Standing)
    {X : Finset (Fin I.n)} (hX : I.IsExactCover X)
    {σ : Fin (4 * I.n) ≃ OrigEdge I} (hσ : σ ∈ omegaXC I X)
    (p : Fin (4 * I.n)) :
    stepWeight X (remaining σ (4 * I.n - p.val)) (σ p) = rootMultiplier X (σ p) := by
  classical
  let i := 4 * I.n - p.val
  let e := σ p
  let s := remaining σ i
  have hp := p.isLt
  have hi : i ≤ 4 * I.n := Nat.sub_le ..
  have hclass : e.setIdx ∈ X ↔ i ≤ 4 * I.h := by
    rw [← mem_edgesOf_iff (e := e), ← remaining_cover_eq hI σ hσ, mem_remaining]
    simp only [e, Equiv.symm_apply_apply]
    dsimp [i]
    omega
  have hs : e ∈ s := (mem_remaining σ i e).mpr (by
    simp only [e, Equiv.symm_apply_apply]
    dsimp [i]
    omega)
  have hphase := nonCoverEdges_remaining_nonempty_iff hI σ hX hσ i hi
  change (nonCoverEdges X s).Nonempty ↔ _ at hphase
  have hactive : e ∈ activeEdges X s := by
    unfold activeEdges
    split <;> rename_i h
    · exact Finset.mem_filter.mpr ⟨hs, fun hx => by have := hclass.mp hx; have := hphase.mp h; omega⟩
    · exact hs
  change stepWeight X s e = rootMultiplier X e
  rw [stepWeight, if_pos hactive, rawWeight, rootMultiplier]
  by_cases hr : e = edgeRoot e
  · rw [if_pos hr, if_pos hr]
    by_cases hc : e.setIdx ∈ X
    · have h := not_lt_of_ge (hclass.mp hc)
      norm_num [phaseBonus, if_pos hc, if_neg (mt hphase.mp h)]
    · have h := Nat.lt_of_not_ge (mt hclass.mpr hc)
      simp [phaseBonus, if_neg hc, if_pos (hphase.mpr h)]
  · rw [if_neg hr, if_neg hr]
    have ho := (mem_omegaLE_iff_root.mp (Finset.mem_filter.mp hσ).1 e hr)
    have hnot : edgeRoot e ∉ s := by
      intro hrm
      have hh := (mem_remaining σ i (edgeRoot e)).mp hrm
      change (σ.symm (edgeRoot e)).val < (σ.symm e).val at ho
      simp only [e, Equiv.symm_apply_apply] at ho
      dsimp [i, e] at hh
      omega
    exact if_neg (fun hh => hnot (activeEdges_subset X s hh))

private theorem prod_step_rates {I : X3CInstance} (hI : I.Standing)
    {X : Finset (Fin I.n)} (hX : I.IsExactCover X)
    {σ : Fin (4 * I.n) ≃ OrigEdge I} (hσ : σ ∈ omegaXC I X) :
    (∏ p : Fin (4 * I.n), edgeRate X (remaining σ (4 * I.n - p.val)) (σ p)) =
      ((4 : ℝ) ^ I.h * (3 : ℝ) ^ (I.n-I.h)) *
        (∏ i ∈ Finset.Icc (4*I.h+1) (4*I.n), 1 / ((i : ℝ) - Ccount σ i)) /
          ((4*I.h).factorial : ℝ) := by
  classical
  let f : ℕ → ℝ := fun i =>
    1 / (if i ≤ 4*I.h then (i : ℝ) else (i : ℝ) - Ccount σ i)
  calc
    _ = ∏ p : Fin (4 * I.n), rootMultiplier X (σ p) * f (4 * I.n - p.val) := by
      apply Finset.prod_congr rfl
      intro p _
      let i := 4 * I.n - p.val
      change edgeRate X (remaining σ i) (σ p) = rootMultiplier X (σ p) * f i
      rw [edgeRate, weight_num_eq_multiplier hI hX hσ p,
        sumStepWeights_remaining hI σ hX hσ i (Nat.sub_le ..)]
      simp [f, div_eq_mul_inv]
    _ = ((4 : ℝ) ^ I.h * (3 : ℝ) ^ (I.n-I.h)) *
          (∏ i ∈ Finset.Icc 1 (4*I.n), f i) := by
      rw [Finset.prod_mul_distrib, prod_by_reverse_positions]
      rw [Fintype.prod_equiv σ _ _ (fun _ => rfl), prod_rootMultiplier, hX.1]
    _ = _ := by
      simp only [f, prod_split_suffix hI.2.le, mul_div_assoc]

end CountOrderings.NFree

open CountOrderings.NFree in
theorem solution (I : X3CInstance) (hI : I.Standing) (X : Finset (Fin I.n))
    (hX : X ∈ I.exactCovers) :
    ∑ σ ∈ omegaXC I X,
        ∏ i ∈ Finset.Icc (4 * I.h + 1) (4 * I.n), 1 / ((i : ℝ) - (Ccount σ i : ℝ)) =
      ((4 * I.h).factorial : ℝ) / ((4 : ℝ) ^ I.h * (3 : ℝ) ^ (I.n - I.h)) := by
  classical
  have hx : I.IsExactCover X := (Finset.mem_filter.mp hX).2
  let c : ℝ := (4 : ℝ)^I.h * (3 : ℝ)^(I.n-I.h)
  let F : ℝ := ((4*I.h).factorial : ℝ)
  let w : (Fin (4*I.n) ≃ OrigEdge I) → ℝ := fun σ =>
    ∏ i ∈ Finset.Icc (4*I.h+1) (4*I.n), 1 / ((i : ℝ) - Ccount σ i)
  have hc : c ≠ 0 := by dsimp [c]; positivity
  have hF : F ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hm : c * (∑ σ ∈ omegaXC I X, w σ) / F = 1 := by
    rw [Finset.mul_sum, Finset.sum_div]
    calc
      _ = ∑ σ ∈ omegaXC I X, ∏ p : Fin (4*I.n),
          edgeRate X (remaining σ (4*I.n-p.val)) (σ p) := by
        apply Finset.sum_congr rfl
        intro σ hσ
        exact (prod_step_rates hI hx hσ).symm
      _ = 1 := sum_omegaXC_pathRates I hI X hX
  change (∑ σ ∈ omegaXC I X, w σ) = F / c
  apply (eq_div_iff hc).mpr
  simpa [mul_comm] using (div_eq_iff hF).mp hm
