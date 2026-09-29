-- Prove2me | solution 1 for CompetitivePaging.EATR.adversary_phase_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:22:35.333997+00:00
-- url     : https://prove2.me/submissions/47fffe7c-c734-4934-a6a1-d915a2584537

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_CompetitivePaging_EATR_eatr

open scoped ENNReal


namespace CompetitivePaging.EATR

section Gen
variable {α β : Type*}

lemma tsum_map_mul (μ : PMF α) (f : α → β) (g : β → ℝ≥0∞) :
    ∑' b, μ.map f b * g b = ∑' a, μ a * g (f a) := by
  simp_rw [PMF.map_apply, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  congr 1; funext a
  rw [tsum_eq_single (f a)]
  · simp
  · intro b hb; simp [hb]

lemma tsum_pure_mul (x : α) (g : α → ℝ≥0∞) : ∑' b, PMF.pure x b * g b = g x := by
  rw [tsum_eq_single x]
  · simp
  · intro b hb; simp [PMF.pure_apply, hb]

lemma tsum_const_on_support (μ : PMF α) (g : α → ℝ≥0∞) (c : ℝ≥0∞)
    (h : ∀ a, μ a ≠ 0 → g a = c) : ∑' a, μ a * g a = c := by
  have : ∀ a, μ a * g a = μ a * c := by
    intro a
    by_cases ha : μ a = 0
    · simp [ha]
    · rw [h a ha]
  simp_rw [this, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

lemma unif_congr {s t : Finset α} (hst : s = t) (hs : s.Nonempty) (ht : t.Nonempty) :
    PMF.uniformOfFinset s hs = PMF.uniformOfFinset t ht := by subst hst; rfl

end Gen

variable {M : Type*} [DecidableEq M]

lemma bookAfter_append (a b : M) (l : List M) (r : M) :
    bookAfter a b (l ++ [r]) = bookStep (bookAfter a b l) r := by
  simp [bookAfter, List.foldl_append]

lemma lawAfter_append (a b : M) (l : List M) (r : M) :
    lawAfter a b (l ++ [r]) = (lawAfter a b l).bind (fun s => step s r) := by
  simp [lawAfter, List.foldl_append]

def Inv (B : Book M) (p : PMF (State M)) : Prop :=
  B.prev.card = 2 ∧
  (B.inPhase = false → B.req = ∅ ∧ ∃ o, p = PMF.pure ⟨B, o⟩) ∧
  (B.inPhase = true → Disjoint B.prev B.req ∧ B.last ∈ B.req ∧
    ∃ h : (stale B).Nonempty, p = (PMF.uniformOfFinset (stale B) h).map (fun y => ⟨B, y⟩))

lemma stale_card (B : Book M) (hd : Disjoint B.prev B.req) (hl : B.last ∈ B.req) :
    (stale B).card + 1 = B.prev.card + B.req.card := by
  unfold stale
  rw [Finset.card_erase_of_mem (Finset.mem_union_right _ hl), Finset.card_union_of_disjoint hd]
  have : 0 < B.req.card := Finset.card_pos.mpr ⟨_, hl⟩
  omega

lemma last_not_mem_stale (B : Book M) : B.last ∉ stale B := by
  simp [stale]

/-- key uniform lemma -/
lemma key_uniform (S : Finset M) (L : M) (hL : L ∉ S) (hS : S.Nonempty) :
    (PMF.uniformOfFinset S hS).bind
      (fun y => (PMF.uniformOfFinset (insert L S) (Finset.insert_nonempty _ _)).map
        (fun z => if z = L then L else y))
      = PMF.uniformOfFinset (insert L S) (Finset.insert_nonempty _ _) := by
  ext x
  rw [PMF.bind_apply]
  have hm : (S.card : ℝ≥0∞) ≠ 0 := by simpa using hS.ne_empty
  have hcT : (insert L S).card = S.card + 1 := Finset.card_insert_of_notMem hL
  have inner : ∀ y ∈ S, ((PMF.uniformOfFinset (insert L S) (Finset.insert_nonempty _ _)).map
        (fun z => if z = L then L else y)) x =
        (if x = L then 1 else 0) / ((S.card : ℝ≥0∞) + 1) +
        (if x = y then (S.card : ℝ≥0∞) else 0) / ((S.card : ℝ≥0∞) + 1) := by
    intro y hy
    have hyL : y ≠ L := fun h => hL (h ▸ hy)
    rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
      PMF.toOuterMeasure_uniformOfFinset_apply, hcT]
    push_cast
    rw [← ENNReal.add_div]
    congr 1
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    by_cases hxL : x = L
    · subst hxL
      have : (insert x S).filter (fun z => (if z = x then x else y) = x) = {x} := by
        ext z; by_cases hz : z = x <;> simp [hz, hyL]
      rw [this]; simp [Ne.symm hyL]
    · by_cases hxy : x = y
      · subst hxy
        have : (insert L S).filter (fun z => (if z = L then L else x) = x) = S := by
          ext z; by_cases hz : z = L
          · subst hz; simp [hL, Ne.symm hxL]
          · simp [hz]
        rw [this]; simp [hxL]
      · have : (insert L S).filter (fun z => (if z = L then L else y) = x) = ∅ := by
          ext z; by_cases hz : z = L
          · subst hz; simp [Ne.symm hxL]
          · simp [hz, Ne.symm hxy]
        rw [this]; simp [hxL, hxy]
  rw [tsum_eq_sum (s := S) (fun y hy => by simp [PMF.uniformOfFinset_apply_of_notMem _ hy])]
  rw [Finset.sum_congr rfl (fun y hy => by rw [PMF.uniformOfFinset_apply_of_mem _ hy, inner y hy])]
  simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [PMF.uniformOfFinset_apply, hcT]
  push_cast
  have hmt : (S.card : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [← mul_assoc, ENNReal.inv_mul_cancel hm hmt, one_mul]
  simp_rw [ite_div, ENNReal.zero_div]
  rw [Finset.sum_ite_eq]
  by_cases hxL : x = L
  · subst hxL
    simp [hL, one_div]
  · by_cases hxS : x ∈ S
    · simp only [hxL, if_false, ENNReal.zero_div, zero_add, hxS, if_true, Finset.mem_insert, or_true]
      rw [div_eq_mul_inv, ← mul_assoc, ENNReal.inv_mul_cancel hm hmt, one_mul]
    · simp [hxL, hxS]

lemma inv_init (a b : M) (hab : a ≠ b) : Inv (initBook a b) (PMF.pure (initState a b)) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [initBook, hab]
  · intro _; exact ⟨rfl, a, rfl⟩
  · intro h; simp [initBook] at h

lemma inv_step (B : Book M) (p : PMF (State M)) (r : M) (hI : Inv B p) :
    Inv (bookStep B r) (p.bind (fun s => step s r)) := by
  obtain ⟨hc, hnp, hp⟩ := hI
  have hne : B.prev.Nonempty := by
    rw [← Finset.card_pos, hc]; norm_num
  cases hB : B.inPhase
  · obtain ⟨hreq, o, rfl⟩ := hnp hB
    rw [PMF.pure_bind]
    by_cases hr : r ∈ B.prev
    · have hbs : bookStep B r = B := by simp [bookStep, hB, hr]
      have hst : step ⟨B, o⟩ r = PMF.pure ⟨B, o⟩ := by simp [step, hB, hr]
      rw [hbs, hst]
      exact ⟨hc, fun _ => ⟨hreq, o, rfl⟩, fun h => by simp [hB] at h⟩
    · have hbs : bookStep B r = ⟨B.prev, true, r, {r}⟩ := by simp [bookStep, hB, hr]
      have hst : step ⟨B, o⟩ r = (PMF.uniformOfFinset B.prev hne).map
          (fun x => ⟨bookStep B r, x⟩) := by simp [step, hB, hr, hne]
      rw [hst, hbs]
      have hsB : stale (⟨B.prev, true, r, {r}⟩ : Book M) = B.prev := by
        simp only [stale]
        rw [Finset.union_comm, ← Finset.insert_eq, Finset.erase_insert hr]
      refine ⟨hc, fun h => by simp at h, fun _ => ⟨?_, by simp, ?_⟩⟩
      · simpa using hr
      · have h2 : (stale (⟨B.prev, true, r, {r}⟩ : Book M)).Nonempty := by rw [hsB]; exact hne
        refine ⟨h2, ?_⟩
        rw [unif_congr hsB h2 hne]
  · obtain ⟨hd, hl, hS, rfl⟩ := hp hB
    rw [PMF.bind_map]
    by_cases hr1 : r = B.last
    · have hbs : bookStep B r = B := by simp [bookStep, hB, hr1]
      have hst : ((fun s => step s r) ∘ fun y => (⟨B, y⟩ : State M)) =
          fun y => PMF.pure ⟨B, y⟩ := by
        funext y; simp [step, hB, hr1]
      rw [hst, hbs]
      exact ⟨hc, fun h => by simp [hB] at h, fun _ => ⟨hd, hl, hS, rfl⟩⟩
    by_cases hr2 : r ∉ B.prev ∪ B.req
    · have hbs : bookStep B r = ⟨B.prev, true, r, insert r B.req⟩ := by
        simp [bookStep, hB, hr1, hr2]
      have hst : ((fun s => step s r) ∘ fun y => (⟨B, y⟩ : State M)) =
          fun y => (PMF.uniformOfFinset (insert B.last (stale B)) (Finset.insert_nonempty _ _)).map
            (fun z => (⟨bookStep B r, if z = B.last then B.last else y⟩ : State M)) := by
        funext y; simp only [Function.comp, step, hB, hr1, hr2]; simp
      rw [hst]
      have hmap : (PMF.uniformOfFinset (stale B) hS).bind (fun y =>
          (PMF.uniformOfFinset (insert B.last (stale B)) (Finset.insert_nonempty _ _)).map
            (fun z => (⟨bookStep B r, if z = B.last then B.last else y⟩ : State M))) =
          ((PMF.uniformOfFinset (stale B) hS).bind (fun y =>
          (PMF.uniformOfFinset (insert B.last (stale B)) (Finset.insert_nonempty _ _)).map
            (fun z => if z = B.last then B.last else y))).map (fun w => ⟨bookStep B r, w⟩) := by
        rw [PMF.map_bind]
        congr 1; funext y
        rw [PMF.map_comp]; rfl
      rw [hmap, key_uniform _ _ (last_not_mem_stale B) hS, hbs]
      have hsB : stale (⟨B.prev, true, r, insert r B.req⟩ : Book M) = insert B.last (stale B) := by
        simp only [stale]
        rw [Finset.insert_erase (Finset.mem_union_right _ hl), Finset.union_insert,
          Finset.erase_insert (by simpa using hr2)]
      have hrp : r ∉ B.prev := fun h => hr2 (Finset.mem_union_left _ h)
      have hrq : r ∉ B.req := fun h => hr2 (Finset.mem_union_right _ h)
      refine ⟨hc, fun h => by simp at h, fun _ => ⟨?_, by simp, ?_⟩⟩
      · simpa [Finset.disjoint_insert_right, hrp] using hd
      · have h2 : (stale (⟨B.prev, true, r, insert r B.req⟩ : Book M)).Nonempty := by
          rw [hsB]; exact Finset.insert_nonempty _ _
        refine ⟨h2, ?_⟩
        rw [unif_congr hsB h2 (Finset.insert_nonempty _ _)]
    · push_neg at hr2
      have hbs : bookStep B r = ⟨{B.last, r}, false, r, ∅⟩ := by
        simp [bookStep, hB, hr1, hr2]
      have hst : ((fun s => step s r) ∘ fun y => (⟨B, y⟩ : State M)) =
          fun _ => PMF.pure ⟨bookStep B r, B.last⟩ := by
        funext y; simp only [Function.comp, step, hB, hr1, hr2, if_true, if_false,
          not_true_eq_false]
      rw [hst, PMF.bind_const, hbs]
      refine ⟨?_, fun _ => ⟨rfl, B.last, rfl⟩, fun h => by simp at h⟩
      simp [Finset.card_pair (Ne.symm hr1)]

lemma inv_after (a b : M) (hab : a ≠ b) (l : List M) :
    Inv (bookAfter a b l) (lawAfter a b l) := by
  induction l using List.reverseRecOn with
  | nil => exact inv_init a b hab
  | append_singleton l r ih =>
    rw [bookAfter_append, lawAfter_append]; exact inv_step _ _ r ih

lemma take_succ_get (σ : List M) (t : ℕ) (h : t < σ.length) :
    σ.take (t + 1) = σ.take t ++ [σ.get ⟨t, h⟩] := by
  rw [List.take_succ_eq_append_getElem h]; rfl

lemma book_succ (a b : M) (σ : List M) (t : ℕ) (h : t < σ.length) :
    bookAfter a b (σ.take (t + 1)) = bookStep (bookAfter a b (σ.take t)) (σ.get ⟨t, h⟩) := by
  rw [take_succ_get σ t h, bookAfter_append]

lemma law_succ (a b : M) (σ : List M) (t : ℕ) (h : t < σ.length) :
    lawAfter a b (σ.take (t + 1)) =
      (lawAfter a b (σ.take t)).bind (fun s => step s (σ.get ⟨t, h⟩)) := by
  rw [take_succ_get σ t h, lawAfter_append]

open Classical in
noncomputable def cnt (a b : M) (σ : List M) (i u : ℕ) : ℕ :=
  ((Finset.Ico i u).filter (fun t => IsCleanRequest a b σ t)).card

open Classical in
lemma cnt_succ (a b : M) (σ : List M) (i u : ℕ) (hu : i ≤ u) :
    cnt a b σ i (u + 1) = cnt a b σ i u + (if IsCleanRequest a b σ u then 1 else 0) := by
  classical
  unfold cnt
  rw [← Nat.succ_eq_add_one, Nat.Ico_succ_right_eq_insert_Ico hu, Finset.filter_insert]
  split_ifs with hc
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rfl

/-- Facts along a complete phase. -/
lemma phase_facts (a b : M) (hab : a ≠ b) (σ : List M) (i i' : ℕ)
    (hph : IsCompletePhase a b σ i i') :
    ∀ u, i + 1 ≤ u → u ≤ i' - 1 →
      (bookAfter a b (σ.take u)).inPhase = true ∧
      (bookAfter a b (σ.take u)).prev = (bookAfter a b (σ.take i)).prev ∧
      (bookAfter a b (σ.take u)).req.card = cnt a b σ i u := by
  obtain ⟨hii, ⟨hi, hBi, hri⟩, hend, hno⟩ := hph
  intro u hu1 hu2
  induction u, hu1 using Nat.le_induction with
  | base =>
    obtain ⟨_, hnp, _⟩ := inv_after a b hab (σ.take i)
    obtain ⟨hreq, _⟩ := hnp hBi
    rw [book_succ a b σ i hi]
    simp only [bookStep, hBi, hri, if_false, Bool.false_eq_true]
    refine ⟨trivial, by first | rfl | trivial, ?_⟩
    rw [cnt_succ a b σ i i le_rfl]
    simp only [cnt, Finset.Ico_self, Finset.filter_empty, Finset.card_empty, zero_add]
    rw [if_pos ⟨hi, by simp only [IsClean, hreq, Finset.union_empty]; exact hri⟩]
    simp
  | succ u hu ih =>
    have hu' : u < i' - 1 := by omega
    obtain ⟨h1, h2, h3⟩ := ih (by omega)
    have hlt : u < σ.length := by
      obtain ⟨hl', _⟩ := hend
      omega
    have hne := hno u (by omega) hu'
    set B := bookAfter a b (σ.take u) with hBdef
    set r := σ.get ⟨u, hlt⟩ with hrdef
    have hns : r ∉ stale B := fun h => hne ⟨hlt, h1, h⟩
    obtain ⟨_, _, hp⟩ := inv_after a b hab (σ.take u)
    obtain ⟨hd, hl, _⟩ := hp h1
    rw [book_succ a b σ u hlt, cnt_succ a b σ i u (by omega)]
    rw [← hBdef, ← hrdef]
    by_cases hr1 : r = B.last
    · have hnc : ¬ IsCleanRequest a b σ u := by
        rintro ⟨h', hc⟩
        apply hc; rw [← hBdef]; show r ∈ _
        rw [hr1]; exact Finset.mem_union_right _ hl
      simp only [bookStep, h1, hr1, if_true, hnc, if_false, add_zero]
      exact ⟨trivial, h2, h3⟩
    · have hr2 : r ∉ B.prev ∪ B.req := by
        intro h; apply hns; simp only [stale]; exact Finset.mem_erase.mpr ⟨hr1, h⟩
      have hc : IsCleanRequest a b σ u := ⟨hlt, hr2⟩
      simp only [bookStep, h1, hr1, hr2, if_true, if_false, hc, not_false_eq_true]
      refine ⟨trivial, h2, ?_⟩
      rw [Finset.card_insert_of_notMem (fun h => hr2 (Finset.mem_union_right _ h)), h3]


lemma phase_end_gt (a b : M) (hab : a ≠ b) (σ : List M) (i i' : ℕ)
    (hph : IsCompletePhase a b σ i i') : i + 1 ≤ i' - 1 := by
  obtain ⟨hii, ⟨hi, hBi, hri⟩, ⟨hf, hBf, _⟩, _⟩ := hph
  by_contra hc
  have : i' - 1 = i := by omega
  rw [this] at hBf; rw [hBf] at hBi; exact Bool.noConfusion hBi

lemma numClean_eq (a b : M) (hab : a ≠ b) (σ : List M) (i i' : ℕ)
    (hph : IsCompletePhase a b σ i i') :
    numClean a b σ i i' = cnt a b σ i (i' - 1) := by
  classical
  have h1 := phase_end_gt a b hab σ i i' hph
  obtain ⟨_, _, ⟨hf, hBf, hs⟩, _⟩ := hph
  have : numClean a b σ i i' = cnt a b σ i (i' - 1 + 1) := by
    rw [Nat.sub_add_cancel (by omega : 1 ≤ i')]; rfl
  rw [this, cnt_succ a b σ i _ (by omega)]
  have hnc : ¬ IsCleanRequest a b σ (i' - 1) := by
    rintro ⟨h', hc⟩
    apply hc
    simp only [stale] at hs
    exact Finset.mem_of_mem_erase hs
  simp [hnc]

theorem phase_stale_uniform_core (a b : M) (hab : a ≠ b)
    (σ : List M) (i i' : ℕ) (hph : IsCompletePhase a b σ i i') :
    (stale (bookAfter a b (σ.take (i' - 1)))).card = numClean a b σ i i' + 1 ∧
      ∀ v ∈ stale (bookAfter a b (σ.take (i' - 1))),
        (lawAfter a b (σ.take (i' - 1))).toOuterMeasure {s | v ∈ servers s}
          = ((numClean a b σ i i' : ℝ≥0∞) + 1)⁻¹ := by
  have h1 := phase_end_gt a b hab σ i i' hph
  have hnc := numClean_eq a b hab σ i i' hph
  obtain ⟨hin, _, hcard⟩ := phase_facts a b hab σ i i' hph (i' - 1) h1 le_rfl
  obtain ⟨hc2, _, hp⟩ := inv_after a b hab (σ.take (i' - 1))
  obtain ⟨hd, hl, hS, hlaw⟩ := hp hin
  have hsc := stale_card _ hd hl
  have hcardS : (stale (bookAfter a b (σ.take (i' - 1)))).card = numClean a b σ i i' + 1 := by
    omega
  refine ⟨hcardS, ?_⟩
  intro v hv
  have hvl : v ≠ (bookAfter a b (σ.take (i' - 1))).last := by
    intro h; rw [h] at hv; exact last_not_mem_stale _ hv
  have hset : (fun y => (⟨bookAfter a b (σ.take (i' - 1)), y⟩ : State M)) ⁻¹'
        {s | v ∈ servers s} = {v} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_setOf_eq, servers, hin, if_true,
      Finset.mem_insert, Finset.mem_singleton, hvl, false_or, Set.mem_singleton_iff]
    exact eq_comm
  rw [hlaw, PMF.toOuterMeasure_map_apply, hset, PMF.toOuterMeasure_apply_singleton,
    PMF.uniformOfFinset_apply_of_mem _ hv, hcardS]
  push_cast; rfl


lemma stepCost_eq (a b : M) (σ : List M) (t : ℕ) (h : t < σ.length) :
    eatrStepCost a b σ t =
      (∑' s : State M, lawAfter a b (σ.take t) s * stepMoves s (σ.get ⟨t, h⟩)).toReal := by
  simp [eatrStepCost, h]

lemma pair_sdiff (r w : M) (S : Finset M) (hw : w ∈ S) (hr : r ∉ S) :
    ({r, w} : Finset M) \ S = {r} := by
  ext x; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨h1 | h1, h2⟩
    · exact h1
    · subst h1; exact absurd hw h2
  · rintro rfl; exact ⟨Or.inl rfl, hr⟩

/-- cost of the phase-start step -/
lemma cost_start (a b : M) (hab : a ≠ b) (σ : List M) (i : ℕ) (hs : IsPhaseStart a b σ i) :
    eatrStepCost a b σ i = 1 := by
  obtain ⟨hi, hBi, hri⟩ := hs
  rw [stepCost_eq a b σ i hi]
  obtain ⟨hc, hnp, _⟩ := inv_after a b hab (σ.take i)
  obtain ⟨hreq, o, hlaw⟩ := hnp hBi
  set B := bookAfter a b (σ.take i)
  set r := σ.get ⟨i, hi⟩
  have hne : B.prev.Nonempty := by rw [← Finset.card_pos, hc]; norm_num
  rw [hlaw, tsum_pure_mul]
  have hst : step ⟨B, o⟩ r = (PMF.uniformOfFinset B.prev hne).map
      (fun x => ⟨bookStep B r, x⟩) := by simp [step, hBi, hri, hne]
  unfold stepMoves
  rw [hst, tsum_map_mul, tsum_const_on_support _ _ 1]
  · simp
  · intro x hx
    rw [← PMF.mem_support_iff, PMF.mem_support_uniformOfFinset_iff] at hx
    have hbs : bookStep B r = ⟨B.prev, true, r, {r}⟩ := by simp [bookStep, hBi, hri]
    simp only [servers, hbs, hBi, if_true, Bool.false_eq_true, if_false]
    rw [pair_sdiff r x B.prev hx hri]; simp

open Classical in
lemma cost_mid (a b : M) (hab : a ≠ b) (σ : List M) (t : ℕ) (h : t < σ.length)
    (hin : (bookAfter a b (σ.take t)).inPhase = true)
    (hns : σ.get ⟨t, h⟩ ∉ stale (bookAfter a b (σ.take t))) :
    eatrStepCost a b σ t = if IsCleanRequest a b σ t then 1 else 0 := by
  rw [stepCost_eq a b σ t h]
  set B := bookAfter a b (σ.take t) with hB
  set r := σ.get ⟨t, h⟩ with hr
  obtain ⟨_, _, hp⟩ := inv_after a b hab (σ.take t)
  rw [← hB] at hp
  obtain ⟨hd, hl, hS, hlaw⟩ := hp hin
  rw [hlaw, tsum_map_mul]
  by_cases hr1 : r = B.last
  · have hnc : ¬ IsCleanRequest a b σ t := by
      rintro ⟨h', hc⟩
      apply hc; show r ∈ _
      rw [hr1]; exact Finset.mem_union_right _ hl
    rw [if_neg hnc, tsum_const_on_support _ _ 0]
    · simp
    · intro y _
      unfold stepMoves
      have hst : step ⟨B, y⟩ r = PMF.pure ⟨B, y⟩ := by simp [step, hin, hr1]
      rw [hst, tsum_pure_mul]; simp
  · have hr2 : r ∉ B.prev ∪ B.req := by
      intro h; apply hns; simp only [stale]; exact Finset.mem_erase.mpr ⟨hr1, h⟩
    have hc : IsCleanRequest a b σ t := ⟨h, hr2⟩
    rw [if_pos hc, tsum_const_on_support _ _ 1]
    · simp
    · intro y hy
      rw [← PMF.mem_support_iff, PMF.mem_support_uniformOfFinset_iff] at hy
      unfold stepMoves
      have hst : step ⟨B, y⟩ r =
          (PMF.uniformOfFinset (insert B.last (stale B)) (Finset.insert_nonempty _ _)).map
            (fun z => ⟨bookStep B r, if z = B.last then B.last else y⟩) := by
        simp [step, hin, hr1, hr2]
      rw [hst, tsum_map_mul, tsum_const_on_support _ _ 1]
      intro z _
      have hbs : bookStep B r = ⟨B.prev, true, r, insert r B.req⟩ := by
        simp [bookStep, hin, hr1, hr2]
      have hyS : y ∈ B.prev ∪ B.req := by
        simp only [stale] at hy; exact Finset.mem_of_mem_erase hy
      have hrS : r ∉ ({B.last, y} : Finset M) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hr1, fun h => hr2 (h ▸ hyS)⟩
      simp only [servers, hbs, hin, if_true]
      rw [pair_sdiff r _ _ ?_ hrS]
      · simp
      · split_ifs <;> simp

/-- cost of the final step of a phase -/
lemma cost_end (a b : M) (hab : a ≠ b) (σ : List M) (t : ℕ) (he : IsPhaseEnd a b σ t) :
    eatrStepCost a b σ t =
      (((stale (bookAfter a b (σ.take t))).card : ℝ) - 1) /
        ((stale (bookAfter a b (σ.take t))).card : ℝ) := by
  obtain ⟨h, hin, hs⟩ := he
  rw [stepCost_eq a b σ t h]
  set B := bookAfter a b (σ.take t) with hB
  set r := σ.get ⟨t, h⟩ with hr
  obtain ⟨_, _, hp⟩ := inv_after a b hab (σ.take t)
  rw [← hB] at hp
  obtain ⟨hd, hl, hS, hlaw⟩ := hp hin
  have hr1 : r ≠ B.last := fun h => last_not_mem_stale B (h ▸ hs)
  have hr2 : r ∈ B.prev ∪ B.req := Finset.mem_of_mem_erase hs
  rw [hlaw, tsum_map_mul]
  have hinner : ∀ y, stepMoves ⟨B, y⟩ r = if y = r then 0 else 1 := by
    intro y
    unfold stepMoves
    have hst : step ⟨B, y⟩ r = PMF.pure ⟨bookStep B r, B.last⟩ := by
      simp [step, hin, hr1, hr2]
    have hbs : bookStep B r = ⟨{B.last, r}, false, r, ∅⟩ := by
      simp [bookStep, hin, hr1, hr2]
    rw [hst, tsum_pure_mul]
    simp only [servers, hbs, hin, if_true, Bool.false_eq_true, if_false]
    by_cases hy : y = r
    · subst hy; simp
    · rw [if_neg hy]
      have : ({B.last, r} : Finset M) \ {B.last, y} = {r} := by
        ext x; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨h1 | h1, h2⟩
          · exact absurd (Or.inl h1) h2
          · exact h1
        · rintro rfl; exact ⟨Or.inr rfl, fun h => h.elim hr1 (fun h => hy h.symm)⟩
      rw [this]; simp
  simp_rw [hinner]
  rw [tsum_eq_sum (s := stale B) (fun y hy => by simp [PMF.uniformOfFinset_apply_of_notMem _ hy])]
  rw [Finset.sum_congr rfl (fun y hy => by rw [PMF.uniformOfFinset_apply_of_mem _ hy])]
  rw [← Finset.mul_sum, ← Finset.sum_erase_add _ _ hs]
  rw [Finset.sum_congr rfl (fun y hy => by
    rw [if_neg (Finset.mem_erase.mp hy).1])]
  simp only [if_true, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [Finset.card_erase_of_mem hs]
  have hpos : 1 ≤ (stale B).card := Finset.card_pos.mpr ⟨r, hs⟩
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv]
  simp only [ENNReal.toReal_natCast]
  rw [Nat.cast_sub hpos]; push_cast; ring

theorem eatr_phase_cost_core (a b : M) (hab : a ≠ b)
    (σ : List M) (i i' : ℕ) (hph : IsCompletePhase a b σ i i') :
    eatrPhaseCost a b σ i i'
      = (numClean a b σ i i' : ℝ) + (numClean a b σ i i' : ℝ) / ((numClean a b σ i i' : ℝ) + 1) := by
  classical
  have h1 := phase_end_gt a b hab σ i i' hph
  have hnc := numClean_eq a b hab σ i i' hph
  have hsu := (phase_stale_uniform_core a b hab σ i i' hph).1
  obtain ⟨hii, hst, hend, hno⟩ := hph
  have hmid : ∀ t ∈ Finset.Ico i (i' - 1),
      eatrStepCost a b σ t = if IsCleanRequest a b σ t then 1 else 0 := by
    intro t ht
    rw [Finset.mem_Ico] at ht
    rcases Nat.eq_or_lt_of_le ht.1 with h | h
    · rw [← h, cost_start a b hab σ _ hst, if_pos]
      obtain ⟨hi, hBi, hri⟩ := hst
      obtain ⟨_, hnp, _⟩ := inv_after a b hab (σ.take i)
      obtain ⟨hreq, _⟩ := hnp hBi
      refine ⟨hi, ?_⟩
      unfold IsClean; rw [hreq, Finset.union_empty]; exact hri
    · obtain ⟨hin, _, _⟩ := phase_facts a b hab σ i i' ⟨hii, hst, hend, hno⟩ t h (by omega)
      have hlt : t < σ.length := by obtain ⟨h', _⟩ := hend; omega
      exact cost_mid a b hab σ t hlt hin (fun hs => hno t ht.1 ht.2 ⟨hlt, hin, hs⟩)
  unfold eatrPhaseCost
  have hI : i' = (i' - 1) + 1 := by omega
  rw [hI, Finset.sum_Ico_succ_top (by omega : i ≤ i' - 1), ← hI, Finset.sum_congr rfl hmid,
    cost_end a b hab σ _ hend, hsu]
  rw [Finset.sum_boole, hnc]
  unfold cnt
  push_cast; ring


lemma phase_req (a b : M) (hab : a ≠ b) (σ : List M) (i i' : ℕ)
    (hph : IsCompletePhase a b σ i i') :
    ∀ u, i + 1 ≤ u → u ≤ i' - 1 →
      (∀ s (hs : s < σ.length), i ≤ s → s < u → σ.get ⟨s, hs⟩ ∈ (bookAfter a b (σ.take u)).req) ∧
      (∀ hu : u - 1 < σ.length, (bookAfter a b (σ.take u)).last = σ.get ⟨u - 1, hu⟩) := by
  have hph' := hph
  obtain ⟨hii, ⟨hi, hBi, hri⟩, hend, hno⟩ := hph
  intro u hu1 hu2
  induction u, hu1 using Nat.le_induction with
  | base =>
    rw [book_succ a b σ i hi]
    simp only [bookStep, hBi, hri, if_false, Bool.false_eq_true]
    refine ⟨fun s hs h1 h2 => ?_, fun hu => ?_⟩
    · have : s = i := by omega
      subst this; simp
    · simp
  | succ u hu ih =>
    have hu' : u < i' - 1 := by omega
    obtain ⟨h1, _, _⟩ := phase_facts a b hab σ i i' hph' u hu (by omega)
    obtain ⟨ihr, ihl⟩ := ih (by omega)
    have hlt : u < σ.length := by
      obtain ⟨hl', _⟩ := hend
      omega
    have hne := hno u (by omega) hu'
    set B := bookAfter a b (σ.take u) with hBdef
    set r := σ.get ⟨u, hlt⟩ with hrdef
    have hns : r ∉ stale B := fun h => hne ⟨hlt, h1, h⟩
    obtain ⟨_, _, hp⟩ := inv_after a b hab (σ.take u)
    obtain ⟨hd, hl, _⟩ := hp h1
    rw [book_succ a b σ u hlt, ← hBdef, ← hrdef]
    by_cases hr1 : r = B.last
    · simp only [bookStep, h1, hr1, if_true]
      refine ⟨fun s hs hs1 hs2 => ?_, fun _ => ?_⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hs2 with h | h
        · exact ihr s hs hs1 h
        · subst h; show r ∈ B.req; rw [hr1]; exact hl
      · rw [← hr1]; rfl
    · have hr2 : r ∉ B.prev ∪ B.req := by
        intro h; apply hns; simp only [stale]; exact Finset.mem_erase.mpr ⟨hr1, h⟩
      simp only [bookStep, h1, hr1, hr2, if_true, if_false, not_false_eq_true]
      refine ⟨fun s hs hs1 hs2 => ?_, fun _ => rfl⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hs2 with h | h
      · exact Finset.mem_insert_of_mem (ihr s hs hs1 h)
      · subst h; exact Finset.mem_insert_self _ _

lemma clean_facts (a b : M) (hab : a ≠ b) (σ : List M) (i i' : ℕ)
    (hph : IsCompletePhase a b σ i i') (t : ℕ) (ht1 : i ≤ t) (ht2 : t ≤ i' - 1)
    (hc : IsCleanRequest a b σ t) :
    ∃ h : t < σ.length, σ.get ⟨t, h⟩ ∉ (bookAfter a b (σ.take i)).prev ∧
      ∀ s (hs : s < σ.length), i ≤ s → s < t → σ.get ⟨s, hs⟩ ≠ σ.get ⟨t, h⟩ := by
  obtain ⟨h, hcl⟩ := hc
  refine ⟨h, ?_⟩
  rcases Nat.eq_or_lt_of_le ht1 with he | hlt
  · subst he
    refine ⟨fun hm => hcl (Finset.mem_union_left _ hm), fun s hs h1 h2 => by omega⟩
  · obtain ⟨_, hprev, _⟩ := phase_facts a b hab σ i i' hph t hlt ht2
    obtain ⟨hreq, _⟩ := phase_req a b hab σ i i' hph t hlt ht2
    refine ⟨fun hm => hcl (Finset.mem_union_left _ (hprev ▸ hm)), fun s hs h1 h2 he => ?_⟩
    exact hcl (Finset.mem_union_right _ (he ▸ hreq s hs h1 h2))

section Adv
variable [MetricSpace M]

lemma lazy_step (A : KServer.OnlineAlgorithm 2 M) (hA : IsLazy A) (l : List M) (r : M) :
    ((∃ k, A.conf l k = r) ∧ A.conf (l ++ [r]) = A.conf l) ∨
    ((¬ ∃ k, A.conf l k = r) ∧ ∃ k, A.conf (l ++ [r]) = Function.update (A.conf l) k r) := by
  by_cases h : ∃ k, A.conf l k = r
  · exact Or.inl ⟨h, hA.1 l r h⟩
  · exact Or.inr ⟨h, hA.2 l r⟩

lemma lazy_cost (hunif : ∀ x y : M, x ≠ y → dist x y = 1)
    (A : KServer.OnlineAlgorithm 2 M) (hA : IsLazy A) (l : List M) (r : M) :
    KServer.moveCost (A.conf l) (A.conf (l ++ [r])) = if (∃ k, A.conf l k = r) then 0 else 1 := by
  classical
  rcases lazy_step A hA l r with ⟨h, he⟩ | ⟨h, k, he⟩
  · rw [if_pos h, he]; simp [KServer.moveCost]
  · rw [if_neg h, he]
    unfold KServer.moveCost
    rw [Finset.sum_eq_single k]
    · simp only [Function.update_self]
      exact hunif _ _ (fun hh => h ⟨k, hh⟩)
    · intro j _ hj; simp [Function.update_of_ne hj]
    · simp

lemma lazy_back (A : KServer.OnlineAlgorithm 2 M) (hA : IsLazy A) (l : List M) (r x : M)
    (k : Fin 2) (h : A.conf (l ++ [r]) k = x) (hr : r ≠ x) : A.conf l k = x := by
  rcases lazy_step A hA l r with ⟨_, he⟩ | ⟨_, k', he⟩
  · rw [he] at h; exact h
  · rw [he] at h
    by_cases hk : k = k'
    · subst hk; simp at h; exact absurd h hr
    · rwa [Function.update_of_ne hk] at h

lemma lazy_back_iter (A : KServer.OnlineAlgorithm 2 M) (hA : IsLazy A) (σ : List M)
    (i t : ℕ) (ht : t < σ.length) (hit : i ≤ t) (x : M) (k : Fin 2)
    (hx : A.conf (σ.take t) k = x)
    (hne : ∀ s (hs : s < σ.length), i ≤ s → s < t → σ.get ⟨s, hs⟩ ≠ x) :
    A.conf (σ.take i) k = x := by
  have key : ∀ n, n ≤ t - i → A.conf (σ.take (t - n)) k = x := by
    intro n
    induction n with
    | zero => intro _; simpa using hx
    | succ n ih =>
      intro hn
      have h1 := ih (by omega)
      have hs : t - (n + 1) < σ.length := by omega
      have he : t - n = t - (n + 1) + 1 := by omega
      rw [he, take_succ_get σ _ hs] at h1
      exact lazy_back A hA _ _ x k h1 (hne _ hs (by omega) (by omega))
  have := key (t - i) le_rfl
  rwa [show t - (t - i) = i by omega] at this

end Adv


lemma fin2_cases (k k1 k2 : Fin 2) (h : k1 ≠ k2) : k = k1 ∨ k = k2 := by
  revert k k1 k2; decide

section Adv2
variable [MetricSpace M]

open Classical in
lemma alg_cost_eq (hunif : ∀ x y : M, x ≠ y → dist x y = 1)
    (A : KServer.OnlineAlgorithm 2 M) (hA : IsLazy A) (σ : List M) (i i' : ℕ)
    (hlen : i' ≤ σ.length) :
    algPhaseCost A σ i i' = (((Finset.Ico i i').filter (fun j =>
      ¬ ∃ (h : j < σ.length) (k : Fin 2), A.conf (σ.take j) k = σ.get ⟨j, h⟩)).card : ℝ) := by
  unfold algPhaseCost
  rw [Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_Ico] at hj
  have hj' : j < σ.length := by omega
  rw [take_succ_get σ j hj', lazy_cost hunif A hA]
  by_cases hc : ∃ k, A.conf (σ.take j) k = σ.get ⟨j, hj'⟩
  · rw [if_pos hc, if_neg (fun h => h ⟨hj', hc⟩)]; simp
  · rw [if_neg hc, if_pos (fun ⟨_, h⟩ => hc h)]; simp

theorem adversary_phase_bound_core (hunif : ∀ x y : M, x ≠ y → dist x y = 1) (a b : M)
    (hab : a ≠ b)
    (A : KServer.OnlineAlgorithm 2 M) (hA : IsLazy A) (σ : List M) (i i' : ℕ)
    (hph : IsCompletePhase a b σ i i') :
    (numClean a b σ i i' : ℝ) - (mismatch a b A σ i : ℝ) + (mismatch a b A σ i' : ℝ)
      ≤ algPhaseCost A σ i i' := by
  classical
  obtain ⟨f, rfl⟩ : ∃ f, i' = f + 1 := ⟨i' - 1, by have := hph.1; omega⟩
  have h1 := phase_end_gt a b hab σ i _ hph
  have hph' := hph
  simp only [Nat.add_sub_cancel] at h1
  obtain ⟨hii, hst, hend, hno⟩ := hph
  obtain ⟨hf, hinf, hsf⟩ := hend
  simp only [Nat.add_sub_cancel] at hf hinf hsf
  have hlen : (f + 1) ≤ σ.length := by omega
  rw [alg_cost_eq hunif A hA σ i (f + 1) hlen]
  set P : ℕ → Prop := fun j =>
      ∃ (h : j < σ.length) (k : Fin 2), A.conf (σ.take j) k = σ.get ⟨j, h⟩ with hP
  set T := (Finset.Ico i (f + 1)).filter (fun t => IsCleanRequest a b σ t) with hT
  have hnc : numClean a b σ i (f + 1) = T.card := rfl
  set D := Finset.univ.filter (fun k : Fin 2 =>
    A.conf (σ.take i) k ∉ (bookAfter a b (σ.take i)).prev) with hD
  have hd : mismatch a b A σ i = D.card := by
    unfold mismatch; rw [hD]
  set D' := Finset.univ.filter (fun k : Fin 2 =>
    A.conf (σ.take (f + 1)) k ∉ (bookAfter a b (σ.take (f + 1))).prev) with hD'
  have hd' : mismatch a b A σ (f + 1) = D'.card := by
    unfold mismatch; rw [hD']
  -- f not clean
  have hfT : f ∉ T := by
    rw [hT, Finset.mem_filter]
    rintro ⟨_, h', hc⟩
    apply hc
    simp only [stale] at hsf
    exact Finset.mem_of_mem_erase hsf
  -- claim 1
  have c1 : (T.filter P).card ≤ D.card := by
    apply Finset.card_le_card_of_forall_subsingleton
      (fun t k => ∃ h : t < σ.length, A.conf (σ.take t) k = σ.get ⟨t, h⟩)
    · intro t ht
      rw [Finset.mem_filter, hT, Finset.mem_filter, Finset.mem_Ico] at ht
      obtain ⟨⟨⟨ht1, ht2⟩, hc⟩, hPt⟩ := ht
      obtain ⟨h, k, hk⟩ := hPt
      obtain ⟨h', hnP, hne⟩ := clean_facts a b hab σ i (f + 1) hph' t ht1 (by omega) hc
      refine ⟨k, ?_, h, hk⟩
      rw [hD, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [lazy_back_iter A hA σ i t h ht1 _ k hk hne]
      exact hnP
    · intro k _ t1 ht1 t2 ht2
      simp only [Set.mem_setOf_eq, Finset.coe_filter, hT, Finset.mem_filter,
        Finset.mem_Ico] at ht1 ht2
      obtain ⟨⟨⟨⟨ha1, hb1⟩, hc1⟩, _⟩, h1', hk1⟩ := ht1
      obtain ⟨⟨⟨⟨ha2, hb2⟩, hc2⟩, _⟩, h2', hk2⟩ := ht2
      obtain ⟨_, _, hne1⟩ := clean_facts a b hab σ i (f + 1) hph' t1 ha1 (by omega) hc1
      obtain ⟨_, _, hne2⟩ := clean_facts a b hab σ i (f + 1) hph' t2 ha2 (by omega) hc2
      have e1 := lazy_back_iter A hA σ i t1 h1' ha1 _ k hk1 hne1
      have e2 := lazy_back_iter A hA σ i t2 h2' ha2 _ k hk2 hne2
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · exact hne2 t1 h1' ha1 h (e1.symm.trans e2)
      · exact hne1 t2 h2' ha2 h (e2.symm.trans e1)
  -- claim 2
  have c2 : D'.card ≤ if P f then 0 else 1 := by
    obtain ⟨_, hlast⟩ := phase_req a b hab σ i _ hph' f h1 (by omega)
    have hf1 : f - 1 < σ.length := by omega
    have hlastf := hlast hf1
    have hr1 : σ.get ⟨f, hf⟩ ≠ (bookAfter a b (σ.take f)).last :=
      fun h => last_not_mem_stale _ (h ▸ hsf)
    have hr2 : σ.get ⟨f, hf⟩ ∈ (bookAfter a b (σ.take f)).prev ∪ (bookAfter a b (σ.take f)).req :=
      Finset.mem_of_mem_erase hsf
    have hbook : (bookAfter a b (σ.take (f + 1))).prev =
        {(bookAfter a b (σ.take f)).last, σ.get ⟨f, hf⟩} := by
      rw [book_succ a b σ f hf, bookStep, if_pos hinf, if_neg hr1, if_neg (not_not.mpr hr2)]
    obtain ⟨k1, hk1⟩ := A.serves (σ.take f) (σ.get ⟨f, hf⟩)
    rw [← take_succ_get σ f hf] at hk1
    have hk1D : k1 ∉ D' := by
      rw [hD', Finset.mem_filter, hbook, hk1]; simp
    by_cases hPf : P f
    · rw [if_pos hPf]
      obtain ⟨_, kk, hkk⟩ := hPf
      have hsame : A.conf (σ.take (f + 1)) = A.conf (σ.take f) := by
        rw [take_succ_get σ f hf]; exact hA.1 _ _ ⟨kk, hkk⟩
      obtain ⟨k2, hk2⟩ := A.serves (σ.take (f - 1)) (σ.get ⟨f - 1, hf1⟩)
      rw [← take_succ_get σ (f - 1) hf1, show f - 1 + 1 = f by omega, ← hsame] at hk2
      have hk2D : k2 ∉ D' := by
        rw [hD', Finset.mem_filter, hbook, hk2, hlastf]; simp
      have hk12 : k1 ≠ k2 := by
        intro h; subst h
        rw [hk1] at hk2
        exact hr1 (hk2.trans hlastf.symm)
      have : D' = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro k hk
        have : k = k1 ∨ k = k2 := fin2_cases k k1 k2 hk12
        rcases this with rfl | rfl
        · exact hk1D hk
        · exact hk2D hk
      rw [this]; simp
    · rw [if_neg hPf]
      have : D' ⊆ Finset.univ.erase k1 := by
        intro k hk; rw [Finset.mem_erase]; exact ⟨fun h => hk1D (h ▸ hk), Finset.mem_univ _⟩
      have := Finset.card_le_card this
      rw [Finset.card_erase_of_mem (Finset.mem_univ _)] at this
      simpa using this
  -- combine
  have hsplit := Finset.card_filter_add_card_filter_not (s := T) (p := P)
  have hfin : f ∈ Finset.Ico i (f + 1) := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  have c3 : (T.filter (fun t => ¬ P t)).card + (if P f then 0 else 1) ≤
      ((Finset.Ico i (f + 1)).filter (fun j => ¬ P j)).card := by
    by_cases hPf : P f
    · rw [if_pos hPf, add_zero]
      apply Finset.card_le_card
      intro t; simp only [hT, Finset.mem_filter]; tauto
    · rw [if_neg hPf]
      have hsub : insert f (T.filter (fun t => ¬ P t)) ⊆
          (Finset.Ico i (f + 1)).filter (fun j => ¬ P j) := by
        intro t; simp only [Finset.mem_insert, hT, Finset.mem_filter]
        rintro (rfl | h)
        · exact ⟨hfin, hPf⟩
        · tauto
      have := Finset.card_le_card hsub
      rwa [Finset.card_insert_of_notMem (fun h => hfT (Finset.mem_filter.mp h).1)] at this
  rw [hnc, hd, hd']
  have : T.card + D'.card ≤ ((Finset.Ico i (f + 1)).filter (fun j => ¬ P j)).card + D.card := by
    omega
  have : (T.card : ℝ) + D'.card ≤ ((Finset.Ico i (f + 1)).filter (fun j => ¬ P j)).card + D.card := by
    exact_mod_cast this
  linarith

end Adv2

end CompetitivePaging.EATR

open CompetitivePaging.EATR


theorem solution {M : Type*} [MetricSpace M] [DecidableEq M]
    (hunif : ∀ x y : M, x ≠ y → dist x y = 1) (a b : M) (hab : a ≠ b)
    (A : KServer.OnlineAlgorithm 2 M) (hA : IsLazy A) (σ : List M) (i i' : ℕ)
    (hph : IsCompletePhase a b σ i i') :
    (numClean a b σ i i' : ℝ) - (mismatch a b A σ i : ℝ) + (mismatch a b A σ i' : ℝ)
      ≤ algPhaseCost A σ i i' := by
  exact adversary_phase_bound_core hunif a b hab A hA σ i i' hph
