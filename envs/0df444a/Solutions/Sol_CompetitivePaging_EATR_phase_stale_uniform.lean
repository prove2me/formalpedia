-- Prove2me | solution 1 for CompetitivePaging.EATR.phase_stale_uniform
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:13:14.793986+00:00
-- url     : https://prove2.me/submissions/18871201-af2c-42ac-8dc7-766a601c29f9

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

end CompetitivePaging.EATR

open CompetitivePaging.EATR


theorem solution {M : Type*} [DecidableEq M] (a b : M) (hab : a ≠ b)
    (σ : List M) (i i' : ℕ) (hph : IsCompletePhase a b σ i i') :
    (stale (bookAfter a b (σ.take (i' - 1)))).card = numClean a b σ i i' + 1 ∧
      ∀ v ∈ stale (bookAfter a b (σ.take (i' - 1))),
        (lawAfter a b (σ.take (i' - 1))).toOuterMeasure {s | v ∈ servers s}
          = ((numClean a b σ i i' : ℝ≥0∞) + 1)⁻¹ := by
  exact phase_stale_uniform_core a b hab σ i i' hph
