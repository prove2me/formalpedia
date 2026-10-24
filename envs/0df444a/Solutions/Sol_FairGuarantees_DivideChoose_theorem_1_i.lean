-- Prove2me | solution 1 for FairGuarantees.DivideChoose.theorem_1_i
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T18:59:12.98038+00:00
-- url     : https://prove2.me/submissions/377aa9e2-30aa-4b5e-920c-19ec693b3de7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_FairGuarantees_DivideChoose_Setting
import Definitions.Def_FairGuarantees_DivideChoose_DCRule
import Theorems.Thm_FairGuarantees_DivideChoose_lemma_1
import Theorems.Thm_FairGuarantees_DivideChoose_invariant
import Theorems.Thm_FairGuarantees_DivideChoose_chooser_step
import Theorems.Thm_FairGuarantees_DivideChoose_divider_step

open FairGuarantees.DivideChoose MeasureTheory

namespace DCAux

variable {d n : ℕ}

def pm (a : Fin n) : DCStep d n → Bool := fun s => decide (a ∈ Matched s)

theorem nextAgents_snoc (l : List (DCStep d n)) (s : DCStep d n) :
    nextAgents (l ++ [s]) = s.agents \ Matched s := by
  simp [nextAgents]

theorem nextManna_snoc (Ω : Set (E d)) (l : List (DCStep d n)) (s : DCStep d n) :
    nextManna Ω (l ++ [s]) = s.manna \ ⋃ a ∈ Matched s, assignedPart s a := by
  simp [nextManna]

theorem valid_snoc {Ω : Set (E d)} {l : List (DCStep d n)} {s : DCStep d n}
    (h : IsValidPrefix Ω (l ++ [s])) :
    IsValidPrefix Ω l ∧ s.agents = nextAgents l ∧ s.manna = nextManna Ω l ∧ IsValidStep Ω s := by
  refine ⟨?_, ?_⟩
  · intro k hk
    have := h k (by simp; omega)
    rw [List.getElem_append_left hk] at this
    rwa [List.take_append_of_le_length (by omega)] at this
  · have := h l.length (by simp)
    simp only [List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_cons_zero,
      List.take_left] at this
    exact this

structure Inv (Ω : Set (E d)) (l : List (DCStep d n)) : Prop where
  manna : IsShare Ω (nextManna Ω l)
  old_found : ∀ a ∉ nextAgents l, ∃ t, l.find? (pm a) = some t
  new_none : ∀ a ∈ nextAgents l, l.find? (pm a) = none
  old_share : ∀ a ∉ nextAgents l, IsShare Ω (share l a)
  old_disj : ∀ a ∉ nextAgents l, share l a ∩ nextManna Ω l = ∅
  old_null : ∀ a b, a ∉ nextAgents l → b ∉ nextAgents l → a ≠ b →
    volume (share l a ∩ share l b) = 0
  cover : ∀ x, x ∈ Ω ↔ (x ∈ nextManna Ω l ∨ ∃ a ∉ nextAgents l, x ∈ share l a)

theorem share_eq_of_find (l : List (DCStep d n)) (a : Fin n) (t : DCStep d n)
    (h : l.find? (pm a) = some t) : share l a = assignedPart t a := by
  unfold share; unfold pm at h; rw [h]

theorem find_snoc_old (l : List (DCStep d n)) (s : DCStep d n) (a : Fin n) (t : DCStep d n)
    (h : l.find? (pm a) = some t) : (l ++ [s]).find? (pm a) = some t := by
  rw [List.find?_append, h]; rfl

theorem find_snoc_new (l : List (DCStep d n)) (s : DCStep d n) (a : Fin n)
    (h : l.find? (pm a) = none) : (l ++ [s]).find? (pm a) = [s].find? (pm a) := by
  rw [List.find?_append, h]; rfl

theorem inv_of_valid {Ω : Set (E d)} (hΩ : MeasurableSet Ω) (l : List (DCStep d n))
    (hl : IsValidPrefix Ω l) : Inv Ω l := by
  induction l using List.reverseRecOn with
  | nil =>
    refine ⟨⟨hΩ, subset_rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [nextAgents, nextManna]
  | append_singleton l s ih =>
    obtain ⟨hl', hA, hM, hv⟩ := valid_snoc hl
    have I := ih hl'
    obtain ⟨_, hSs, hPart, _, _, _, ⟨f, hf, hpm⟩, _, _⟩ := hv
    have hass : ∀ a ∈ Matched s, assignedPart s a = s.parts (f a) := by
      intro a ha; simp [assignedPart, hf a ha]
    have hMatchedSub : Matched s ⊆ s.agents := Finset.filter_subset _ _
    -- characterization of share after the step
    have hshare_old : ∀ a ∉ nextAgents l, share (l ++ [s]) a = share l a := by
      intro a ha
      obtain ⟨t, ht⟩ := I.old_found a ha
      rw [share_eq_of_find _ _ _ ht, share_eq_of_find _ _ _ (find_snoc_old l s a t ht)]
    have hshare_new : ∀ a ∈ Matched s, a ∈ nextAgents l →
        share (l ++ [s]) a = assignedPart s a := by
      intro a ha haA
      have h1 := find_snoc_new l s a (I.new_none a haA)
      have h2 : [s].find? (pm a) = some s := by simp [pm, ha]
      rw [share_eq_of_find _ _ _ (h1.trans h2)]
    have hX : (⋃ a ∈ Matched s, assignedPart s a) ⊆ s.manna := by
      intro x hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨a, ha, hx⟩ := hx
      rw [hass a ha] at hx
      exact (hPart.1 (f a)).2 hx
    -- membership in the complement of the new agent set
    have hnotA : ∀ a, a ∉ nextAgents (l ++ [s]) ↔ a ∉ nextAgents l ∨ a ∈ Matched s := by
      intro a
      rw [nextAgents_snoc, Finset.mem_sdiff, ← hA]
      constructor
      · intro h
        by_cases h1 : a ∈ s.agents
        · right; by_contra h2; exact h ⟨h1, h2⟩
        · left; exact h1
      · rintro (h | h) ⟨h1, h2⟩
        · exact h h1
        · exact h2 h
    have hshareS : ∀ a ∉ nextAgents (l ++ [s]), IsShare Ω (share (l ++ [s]) a) ∧
        share (l ++ [s]) a ∩ s.manna = ∅ ∨ (a ∈ Matched s ∧ share (l ++ [s]) a = s.parts (f a)) := by
      intro a ha
      rcases (hnotA a).mp ha with h | h
      · left
        rw [hshare_old a h]
        refine ⟨I.old_share a h, ?_⟩
        rw [hM]; exact I.old_disj a h
      · right
        refine ⟨h, ?_⟩
        rw [hshare_new a h (hA ▸ hMatchedSub h), hass a h]
    have hPS : ∀ a ∈ Matched s, IsShare Ω (assignedPart s a) := by
      intro a ha; rw [hass a ha]; exact (hPart.1 (f a)).1
    have hmemA : ∀ a ∈ Matched s, a ∈ nextAgents l := fun a ha => hA ▸ hMatchedSub ha
    have hsh' : ∀ a ∉ nextAgents (l ++ [s]), IsShare Ω (share (l ++ [s]) a) := by
      intro a ha
      rcases (hnotA a).mp ha with h | h
      · rw [hshare_old a h]; exact I.old_share a h
      · rw [hshare_new a h (hmemA a h)]; exact hPS a h
    have hmeasX : MeasurableSet (⋃ a ∈ Matched s, assignedPart s a) :=
      Finset.measurableSet_biUnion _ (fun a ha => (hPS a ha).1)
    refine ⟨?_, ?_, ?_, hsh', ?_, ?_, ?_⟩
    · rw [nextManna_snoc]
      exact ⟨hSs.1.diff hmeasX, Set.sdiff_subset.trans hSs.2⟩
    · intro a ha
      rcases (hnotA a).mp ha with h | h
      · obtain ⟨t, ht⟩ := I.old_found a h
        exact ⟨t, find_snoc_old l s a t ht⟩
      · refine ⟨s, ?_⟩
        rw [find_snoc_new l s a (I.new_none a (hmemA a h))]
        simp [pm, h]
    · intro a ha
      rw [nextAgents_snoc, Finset.mem_sdiff] at ha
      rw [find_snoc_new l s a (I.new_none a (hA ▸ ha.1))]
      simp [pm, ha.2]
    · intro a ha
      rw [nextManna_snoc]
      rcases (hnotA a).mp ha with h | h
      · rw [hshare_old a h]
        apply Set.eq_empty_of_subset_empty
        rw [← I.old_disj a h, ← hM]
        exact Set.inter_subset_inter_right _ Set.sdiff_subset
      · rw [hshare_new a h (hmemA a h)]
        apply Set.eq_empty_of_subset_empty
        intro x ⟨hx1, hx2⟩
        exact hx2.2 (Set.mem_biUnion h hx1)
    · intro a b ha hb hab
      have key : ∀ a b, a ∉ nextAgents l → b ∈ Matched s →
          share (l ++ [s]) a ∩ share (l ++ [s]) b = ∅ := by
        intro a b h1 h2
        rw [hshare_old a h1, hshare_new b h2 (hmemA b h2)]
        apply Set.eq_empty_of_subset_empty
        rw [← I.old_disj a h1, ← hM]
        exact Set.inter_subset_inter_right _ (hX.trans' (Set.subset_biUnion_of_mem (u := fun a => assignedPart s a) h2))
      rcases (hnotA a).mp ha with h1 | h1 <;> rcases (hnotA b).mp hb with h2 | h2
      · rw [hshare_old a h1, hshare_old b h2]; exact I.old_null a b h1 h2 hab
      · rw [key a b h1 h2]; simp
      · rw [Set.inter_comm, key b a h2 h1]; simp
      · rw [hshare_new a h1 (hmemA a h1), hshare_new b h2 (hmemA b h2), hass a h1, hass b h2]
        apply hPart.2.2
        intro he
        exact hab (hpm.2.2.1.injOn h1 h2 he)
    · intro x
      rw [nextManna_snoc, I.cover x, hM]
      constructor
      · rintro (hx | ⟨a, ha, hx⟩)
        · by_cases hxX : x ∈ ⋃ a ∈ Matched s, assignedPart s a
          · right
            simp only [Set.mem_iUnion] at hxX
            obtain ⟨a, ha, hx'⟩ := hxX
            exact ⟨a, (hnotA a).mpr (Or.inr ha), by rw [hshare_new a ha (hmemA a ha)]; exact hx'⟩
          · left; exact ⟨hx, hxX⟩
        · right
          exact ⟨a, (hnotA a).mpr (Or.inl ha), by rw [hshare_old a ha]; exact hx⟩
      · rintro (hx | ⟨a, ha, hx⟩)
        · left; exact hx.1
        · rw [← I.cover x]
          exact (hsh' a ha).2 hx
theorem build_Q {Ω : Set (E d)} (hΩ : MeasurableSet Ω) (l : List (DCStep d n))
    (hl : IsValidPrefix Ω l) (A' : Finset (Fin n)) (hA : A' = nextAgents l)
    (P : Fin A'.card → Set (E d)) (hP : IsPartition Ω (nextManna Ω l) A'.card P) :
    IsPartition Ω Ω n (fun a => if h : a ∈ A' then P (A'.equivFin ⟨a, h⟩) else share l a) := by
  have I := inv_of_valid hΩ l hl
  subst hA
  refine ⟨?_, ?_, ?_⟩
  · intro a
    by_cases h : a ∈ nextAgents l
    · simp only [h, dite_true]
      exact ⟨(hP.1 _).1, (hP.1 _).1.2⟩
    · simp only [h, dite_false]
      exact ⟨I.old_share a h, (I.old_share a h).2⟩
  · ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨a, ha⟩
      by_cases h : a ∈ nextAgents l
      · simp only [h, dite_true] at ha
        exact (hP.1 _).1.2 ha
      · simp only [h, dite_false] at ha
        exact (I.old_share a h).2 ha
    · intro hx
      rcases (I.cover x).mp hx with hx | ⟨a, ha, hx⟩
      · rw [← hP.2.1] at hx
        simp only [Set.mem_iUnion] at hx
        obtain ⟨r, hr⟩ := hx
        refine ⟨((nextAgents l).equivFin.symm r).1, ?_⟩
        simp only [((nextAgents l).equivFin.symm r).2, dite_true]
        simpa using hr
      · exact ⟨a, by simp only [ha, dite_false]; exact hx⟩
  · intro a b hab
    have key : ∀ a b, a ∈ nextAgents l → b ∉ nextAgents l →
        ∀ r, P r ∩ share l b = ∅ := by
      intro a b _ hb r
      apply Set.eq_empty_of_subset_empty
      rw [← I.old_disj b hb, Set.inter_comm]
      exact Set.inter_subset_inter_right _ (hP.1 r).2
    by_cases h1 : a ∈ nextAgents l <;> by_cases h2 : b ∈ nextAgents l <;>
      simp only [h1, h2, dite_true, dite_false]
    · apply hP.2.2
      intro he
      have := (nextAgents l).equivFin.injective he
      exact hab (congrArg Subtype.val this)
    · rw [key a b h1 h2]; simp
    · rw [Set.inter_comm, key b a h2 h1]; simp
    · exact I.old_null a b h1 h2 hab

theorem old_lt {Ω : Set (E d)} (hΩ : MeasurableSet Ω) (hn : 0 < n) {u : Set (E d) → ℝ}
    (i : Fin n) (l : List (DCStep d n)) (hl : IsValidPrefix Ω l)
    (hstrat : FollowsMinMaxStrategy Ω u i l) (hi : i ∈ nextAgents l) :
    ∀ j ∉ nextAgents l, u (share l j) < minMax Ω u n := by
  intro j hj
  obtain ⟨t, ht⟩ := (inv_of_valid hΩ l hl).old_found j hj
  rw [share_eq_of_find _ _ _ ht]
  have htm : t ∈ l := List.mem_of_find?_eq_some ht
  have hjm : j ∈ Matched t := by
    have := List.find?_some ht
    simpa [pm] using this
  exact FairGuarantees.DivideChoose.invariant hn i l hl hstrat hi t htm j hjm

theorem valid_take {Ω : Set (E d)} (run : List (DCStep d n)) (hrun : IsValidPrefix Ω run) (k : ℕ) :
    IsValidPrefix Ω (run.take k) := by
  intro j hj
  have hj' : j < run.length := by simp at hj; omega
  have h := hrun j hj'
  have e1 : (run.take k)[j] = run[j] := by simp
  have e2 : (run.take k).take j = run.take j := by
    rw [List.take_take]; congr 1; simp at hj; omega
  rw [e1, e2]; exact h

end DCAux

open DCAux

theorem solution {d n : ℕ} (hd : 0 < d) (hn : 0 < n) {Ω : Set (E d)} (hΩ : IsManna Ω)
    {u : Set (E d) → ℝ} (hu : IsUtility Ω u) (i : Fin n) :
    (∀ run : List (DCStep d n), IsValidPrefix Ω run → FollowsMinMaxStrategy Ω u i run →
      i ∈ nextAgents run → (∀ b ∈ nextAgents run, i ≤ b) →
      ∃ P : Fin (nextAgents run).card → Set (E d),
        IsEquipartition Ω u (nextManna Ω run) (nextAgents run).card P) ∧
    (∀ run : List (DCStep d n), IsValidPrefix Ω run → FollowsMinMaxStrategy Ω u i run →
      i ∈ nextAgents run → ¬ (∀ b ∈ nextAgents run, i ≤ b) →
      ∀ P : Fin (nextAgents run).card → Set (E d),
        IsPartition Ω (nextManna Ω run) (nextAgents run).card P →
        ∃ r, minMax Ω u n ≤ u (P r)) ∧
    (∀ run : List (DCStep d n), IsValidRun Ω run → FollowsMinMaxStrategy Ω u i run →
      minMax Ω u n ≤ u (share run i)) := by
  have hΩm : MeasurableSet Ω := hΩ.1
  refine ⟨?_, ?_, ?_⟩
  · intro run hrun _ hi _
    exact FairGuarantees.DivideChoose.lemma_1 hd hΩ hu (inv_of_valid hΩm run hrun).manna
      (Finset.card_pos.mpr ⟨i, hi⟩)
  · intro run hrun hstrat hi _ P hP
    let Q : Fin n → Set (E d) := fun a =>
      if h : a ∈ nextAgents run then P ((nextAgents run).equivFin ⟨a, h⟩) else share run a
    have hQ := build_Q hΩm run hrun (nextAgents run) rfl P hP
    obtain ⟨j, hj, hjv⟩ := FairGuarantees.DivideChoose.chooser_step hn hΩ hu hQ
      (Finset.univ.filter (fun a => a ∉ nextAgents run)) (by
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        simp only [hj, dite_false]
        exact old_lt hΩm hn i run hrun hstrat hi j hj)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hj
    simp only [hj, dite_true] at hjv
    exact ⟨_, hjv⟩
  · intro run ⟨hrun, hend⟩ hstrat
    have hex : ∃ j, i ∉ nextAgents (run.take j) :=
      ⟨run.length, by rw [List.take_length, hend]; simp⟩
    classical
    let N := Nat.find hex
    have hN : i ∉ nextAgents (run.take N) := Nat.find_spec hex
    have hN0 : N ≠ 0 := by
      intro h0
      apply hN; rw [h0]; simp [nextAgents]
    obtain ⟨k, hk⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
    have hik : i ∈ nextAgents (run.take k) := by
      have := Nat.find_min hex (show k < N by omega)
      simpa using this
    have hkl : k < run.length := by
      by_contra hcon
      push_neg at hcon
      rw [List.take_of_length_le hcon, hend] at hik
      simp at hik
    have htk1 : run.take (k+1) = run.take k ++ [run[k]] := by
      rw [List.take_succ, List.getElem?_eq_getElem hkl]; rfl
    have hNk : i ∉ nextAgents (run.take (k+1)) := hk ▸ hN
    rw [htk1, nextAgents_snoc, Finset.mem_sdiff] at hNk
    have hvk := hrun k hkl
    have hiA : i ∈ run[k].agents := by rw [hvk.1]; exact hik
    have hiM : i ∈ Matched run[k] := by
      by_contra h; exact hNk ⟨hiA, h⟩
    have hlk := valid_take run hrun k
    have hsk : FollowsMinMaxStrategy Ω u i (run.take k) :=
      fun s hs => hstrat s (List.mem_of_mem_take hs)
    -- share run i = assignedPart run[k] i
    have hfind : run.find? (pm i) = some run[k] := by
      have h1 : (run.take (k+1)).find? (pm i) = some run[k] := by
        rw [htk1, find_snoc_new _ _ _ ((inv_of_valid hΩm _ hlk).new_none i hik)]
        simp [pm, hiM]
      conv_lhs => rw [← List.take_append_drop (k+1) run]
      rw [List.find?_append, h1]; rfl
    rw [share_eq_of_find _ _ _ hfind]
    obtain ⟨_, _, hPart, _, _, _, ⟨f, hf, hpm⟩, hdiv, _⟩ := hvk.2.2
    have hass : assignedPart run[k] i = run[k].parts (f i) := by
      simp [assignedPart, hf i hiM]
    rw [hass]
    have hsi := hstrat run[k] (List.getElem_mem hkl) hiA
    by_cases hD : IsDivider run[k] i
    · have hE := hsi.1 hD
      have hP' : IsPartition Ω (nextManna Ω (run.take k)) run[k].agents.card run[k].parts := by
        rw [← hvk.2.1]; exact hE.1
      have hQ := build_Q hΩm (run.take k) hlk run[k].agents hvk.1 run[k].parts hP'
      have hres := FairGuarantees.DivideChoose.divider_step hn hΩ hu hQ
        (Finset.univ.filter (fun a => a ∉ run[k].agents))
        ⟨i, by simp [hiA]⟩
        (by
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          simp only [hj, dite_false]
          exact old_lt hΩm hn i (run.take k) hlk hsk hik j (hvk.1 ▸ hj))
        (by
          intro j hj j' hj'
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hj hj'
          simp only [hj, hj', dite_true]
          exact hE.2 _ _)
        i (by simp [hiA])
      simp only [hiA, dite_true] at hres
      rw [hE.2 (f i) _]
      exact hres
    · rw [← (hsi.2 hD (f i))]
      exact hpm.2.2.2.1 i hiM

