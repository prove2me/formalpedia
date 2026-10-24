-- Prove2me | solution 1 for FairGuarantees.DivideChoose.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T19:07:26.045233+00:00
-- url     : https://prove2.me/submissions/8688dd9c-ce7e-4143-bc36-883b7f65e999

import Mathlib
import Definitions.Def_FairGuarantees_DivideChoose_Setting
import Definitions.Def_FairGuarantees_DivideChoose_DCRule

open FairGuarantees.DivideChoose

namespace DCL2

variable {α β : Type*} [DecidableEq α]

theorem extend (M : Finset α) (R : Finset β) (likes : α → β → Prop)
    (M1 : Finset α) (R1 : Finset β) (f1 : α → β) (h1 : IsProperMatch M R likes M1 R1 f1)
    (N : Finset α) (T : Finset β) (g : α → β) [DecidableEq β]
    (hNM : N ⊆ M) (hN1 : ∀ a ∈ N, a ∉ M1) (hTR : T ⊆ R) (hT1 : ∀ t ∈ T, t ∉ R1)
    (hbij : Set.BijOn g (N : Set α) (T : Set β)) (hlk : ∀ a ∈ N, likes a (g a))
    (hprop : ∀ a ∈ M \ (M1 ∪ N), ∀ t ∈ T, ¬ likes a t) :
    IsProperMatch M R likes (M1 ∪ N) (R1 ∪ T) (fun a => if a ∈ M1 then f1 a else g a) := by
  obtain ⟨hM1, hR1, hb1, hl1, hp1⟩ := h1
  refine ⟨Finset.union_subset hM1 hNM, Finset.union_subset hR1 hTR, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro a ha
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at ha ⊢
    by_cases h : a ∈ M1
    · simp only [h, if_true]; left; exact hb1.mapsTo h
    · simp only [h, if_false]; right
      exact hbij.mapsTo (ha.resolve_left h)
  · intro a ha b hb hab
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at ha hb
    by_cases h1a : a ∈ M1 <;> by_cases h1b : b ∈ M1 <;> simp only [h1a, h1b, if_true, if_false] at hab
    · exact hb1.injOn h1a h1b hab
    · have hbN := hb.resolve_left h1b
      exact absurd (hab ▸ hb1.mapsTo h1a) (hT1 _ (hbij.mapsTo hbN))
    · have haN := ha.resolve_left h1a
      exact absurd (show g a ∈ (R1 : Set β) by rw [hab]; exact hb1.mapsTo h1b) (hT1 _ (hbij.mapsTo haN))
    · exact hbij.injOn (ha.resolve_left h1a) (hb.resolve_left h1b) hab
  · intro r hr
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at hr
    rcases hr with hr | hr
    · obtain ⟨a, ha, rfl⟩ := hb1.surjOn hr
      exact ⟨a, by simp [ha], by simp [show a ∈ M1 from ha]⟩
    · obtain ⟨a, ha, rfl⟩ := hbij.surjOn hr
      have : a ∉ M1 := hN1 a ha
      exact ⟨a, by simp [show a ∈ N from ha], by simp [this]⟩
  · intro a ha
    rw [Finset.mem_union] at ha
    by_cases h : a ∈ M1
    · simp only [h, if_true]; exact hl1 a h
    · simp only [h, if_false]; exact hlk a (ha.resolve_left h)
  · intro a ha r hr
    rw [Finset.mem_union] at hr
    rcases hr with hr | hr
    · have : a ∈ M \ M1 := by
        rw [Finset.mem_sdiff] at ha ⊢
        exact ⟨ha.1, fun h => ha.2 (Finset.mem_union_left _ h)⟩
      exact hp1 a this r hr
    · exact hprop a ha r hr

theorem union_pm (M : Finset α) (R : Finset β) (likes : α → β → Prop) [DecidableEq β]
    (M1 : Finset α) (R1 : Finset β) (f1 : α → β) (h1 : IsProperMatch M R likes M1 R1 f1)
    (M2 : Finset α) (R2 : Finset β) (f2 : α → β) (h2 : IsProperMatch M R likes M2 R2 f2) :
    ∃ R' g, IsProperMatch M R likes (M1 ∪ M2) R' g := by
  have e : M1 ∪ M2 = M1 ∪ (M2 \ M1) := by
    ext a; simp only [Finset.mem_union, Finset.mem_sdiff]; tauto
  rw [e]
  obtain ⟨hM2, hR2, hb2, hl2, hp2⟩ := h2
  refine ⟨_, _, extend M R likes M1 R1 f1 h1 (M2 \ M1) ((M2 \ M1).image f2) f2
    (Finset.sdiff_subset.trans hM2) (fun a ha => (Finset.mem_sdiff.mp ha).2) ?_ ?_ ?_ ?_ ?_⟩
  · intro r hr
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hr
    exact hR2 (hb2.mapsTo (Finset.mem_sdiff.mp hb).1)
  · intro r hr hrR1
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hr
    rw [Finset.mem_sdiff] at hb
    exact h1.2.2.2.2 b (Finset.mem_sdiff.mpr ⟨hM2 hb.1, hb.2⟩) _ hrR1 (hl2 b hb.1)
  · rw [Finset.coe_image]
    exact (hb2.injOn.mono (by intro x hx; exact (Finset.mem_sdiff.mp hx).1)).bijOn_image
  · intro a ha; exact hl2 a (Finset.mem_sdiff.mp ha).1
  · intro a ha r hr
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hr
    have : a ∈ M \ M2 := by
      rw [Finset.mem_sdiff] at ha ⊢
      refine ⟨ha.1, fun h => ha.2 ?_⟩
      by_cases h' : a ∈ M1
      · exact Finset.mem_union_left _ h'
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨h, h'⟩)
    exact hp2 a this _ (hb2.mapsTo (Finset.mem_sdiff.mp hb).1)

theorem core (M0 : Finset α) (R0 : Finset β) (likes : α → β → Prop) [DecidableEq β]
    (hcard : M0.card = R0.card) (istar : α) (hi : istar ∈ M0) (hall : ∀ r ∈ R0, likes istar r)
    (r0 : β) :
    ∃ N T g, IsProperMatch M0 R0 likes N T g ∧ istar ∈ N := by
  classical
  let N0 : Finset β → Finset α := fun T => M0.filter (fun a => ∃ t ∈ T, likes a t)
  have hN0mono : ∀ T T', T ⊆ T' → N0 T ⊆ N0 T' := by
    intro T T' h a ha
    simp only [N0, Finset.mem_filter] at ha ⊢
    obtain ⟨h1, t, ht, hl⟩ := ha
    exact ⟨h1, t, h ht, hl⟩
  have hstar : ∀ T, T ⊆ R0 → T.Nonempty → istar ∈ N0 T := by
    intro T hT ⟨t, ht⟩
    simp only [N0, Finset.mem_filter]
    exact ⟨hi, t, ht, hall t (hT ht)⟩
  let F := R0.powerset.filter (fun T => T.Nonempty ∧ (N0 T).card ≤ T.card)
  have hR0F : R0 ∈ F := by
    simp only [F, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨subset_rfl, ?_, ?_⟩
    · rw [← Finset.card_pos, ← hcard]; exact Finset.card_pos.mpr ⟨istar, hi⟩
    · rw [← hcard]; exact Finset.card_le_card (Finset.filter_subset _ _)
  obtain ⟨T, hTF, hTmin⟩ := Finset.exists_min_image F Finset.card ⟨R0, hR0F⟩
  simp only [F, Finset.mem_filter, Finset.mem_powerset] at hTF
  obtain ⟨hTR, hTne, hTle⟩ := hTF
  have hmin : ∀ T', T' ⊆ R0 → T'.Nonempty → T'.card < T.card → T'.card < (N0 T').card := by
    intro T' h1 h2 h3
    by_contra hc
    push Not at hc
    have := hTmin T' (by simp only [F, Finset.mem_filter, Finset.mem_powerset]; exact ⟨h1, h2, hc⟩)
    omega
  have hNT : (N0 T).card = T.card := by
    refine le_antisymm hTle ?_
    by_contra hlt
    push Not at hlt
    obtain ⟨t, ht⟩ := hTne
    by_cases h1 : (T.erase t).Nonempty
    · have hc1 : (T.erase t).card < T.card := Finset.card_erase_lt_of_mem ht
      have := hmin (T.erase t) ((Finset.erase_subset _ _).trans hTR) h1 hc1
      have h2 := Finset.card_le_card (hN0mono _ _ (Finset.erase_subset t T))
      rw [Finset.card_erase_of_mem ht] at this
      omega
    · rw [Finset.not_nonempty_iff_eq_empty] at h1
      have hT1 : T.card = 1 := by
        have := Finset.card_erase_of_mem ht; rw [h1] at this; simp at this; omega
      have := Finset.card_pos.mpr ⟨istar, hstar T hTR ⟨t, ht⟩⟩
      omega
  -- Hall's theorem
  let tf : T → Finset α := fun x => N0 {x.1}
  have hHall : ∀ s : Finset T, s.card ≤ (s.biUnion tf).card := by
    intro s
    have hbu : s.biUnion tf = N0 (s.map (Function.Embedding.subtype _)) := by
      ext a
      simp only [tf, N0, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_singleton,
        Finset.mem_map, Function.Embedding.coe_subtype]
      constructor
      · rintro ⟨x, hx, h1, t, rfl, hl⟩
        exact ⟨h1, x.1, ⟨x, hx, rfl⟩, hl⟩
      · rintro ⟨h1, t, ⟨x, hx, rfl⟩, hl⟩
        exact ⟨x, hx, h1, x.1, rfl, hl⟩
    rw [hbu]
    set T' := s.map (Function.Embedding.subtype (· ∈ T))
    have hcs : T'.card = s.card := Finset.card_map _
    have hT'T : T' ⊆ T := by
      intro t ht
      simp only [T', Finset.mem_map, Function.Embedding.coe_subtype] at ht
      obtain ⟨x, _, rfl⟩ := ht
      exact x.2
    rw [← hcs]
    by_cases he : T' = ∅
    · rw [he]; simp
    by_cases heq : T' = T
    · rw [heq, hNT]
    · have hlt : T'.card < T.card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hT'T, heq⟩)
      exact (hmin T' (hT'T.trans hTR) (Finset.nonempty_iff_ne_empty.mpr he) hlt).le
  obtain ⟨f, hfinj, hfmem⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective tf).mp hHall
  have hfN : ∀ x : T, f x ∈ M0 ∧ likes (f x) x.1 := by
    intro x
    have := hfmem x
    simp only [tf, N0, Finset.mem_filter, Finset.mem_singleton] at this
    obtain ⟨h1, t, rfl, hl⟩ := this
    exact ⟨h1, hl⟩
  have himg : Finset.univ.image f = N0 T := by
    apply Finset.eq_of_subset_of_card_le
    · intro a ha
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp ha
      simp only [N0, Finset.mem_filter]
      exact ⟨(hfN x).1, x.1, x.2, (hfN x).2⟩
    · rw [hNT, Finset.card_image_of_injective _ hfinj, Finset.card_univ, Fintype.card_coe]
  let g : α → β := fun a => if h : ∃ x : T, f x = a then (h.choose).1 else r0
  have hg : ∀ x : T, g (f x) = x.1 := by
    intro x
    have h : ∃ y : T, f y = f x := ⟨x, rfl⟩
    simp only [g, h, dite_true]
    rw [hfinj h.choose_spec]
  have hNf : ∀ a ∈ N0 T, ∃ x : T, f x = a := by
    intro a ha
    rw [← himg] at ha
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp ha
    exact ⟨x, rfl⟩
  refine ⟨N0 T, T, g, ⟨Finset.filter_subset _ _, hTR, ⟨?_, ?_, ?_⟩, ?_, ?_⟩,
    hstar T hTR hTne⟩
  · intro a ha
    obtain ⟨x, rfl⟩ := hNf a ha
    rw [hg]; exact x.2
  · intro a ha b hb hab
    obtain ⟨x, rfl⟩ := hNf a ha
    obtain ⟨y, rfl⟩ := hNf b hb
    rw [hg, hg] at hab
    rw [Subtype.ext hab]
  · intro t ht
    refine ⟨f ⟨t, ht⟩, ?_, hg _⟩
    show f ⟨t, ht⟩ ∈ N0 T
    rw [← himg]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  · intro a ha
    obtain ⟨x, rfl⟩ := hNf a ha
    rw [hg]; exact (hfN x).2
  · intro a ha t ht hl
    rw [Finset.mem_sdiff] at ha
    apply ha.2
    simp only [N0, Finset.mem_filter]
    exact ⟨ha.1, t, ht, hl⟩

end DCL2

open DCL2

theorem solution {α β : Type*} [DecidableEq α] (M : Finset α) (R : Finset β)
    (likes : α → β → Prop) (hcard : M.card = R.card) (hlike : ∀ a ∈ M, ∃ r ∈ R, likes a r)
    (istar : α) (hi : istar ∈ M) (hall : ∀ r ∈ R, likes istar r) :
    ∃ Mstar : Finset α, Mstar ⊆ M ∧ istar ∈ Mstar ∧
      (∃ (Rstar : Finset β) (f : α → β), IsProperMatch M R likes Mstar Rstar f) ∧
      ∀ (M' : Finset α) (R' : Finset β) (g : α → β), IsProperMatch M R likes M' R' g →
        M' ⊆ Mstar := by
  classical
  obtain ⟨r0, -, -⟩ := hlike istar hi
  let F := M.powerset.filter (fun M' => ∃ (R' : Finset β) (g : α → β), IsProperMatch M R likes M' R' g)
  have hsup : ∀ G ⊆ F, ∃ (R' : Finset β) (g : α → β), IsProperMatch M R likes (G.sup id) R' g := by
    intro G
    induction G using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨∅, fun _ => r0, ?_⟩
      simp only [Finset.sup_empty, Finset.bot_eq_empty]
      refine ⟨Finset.empty_subset _, Finset.empty_subset _, ?_, by simp, by simp⟩
      simp [Set.BijOn, Set.MapsTo, Set.InjOn, Set.SurjOn]
    | insert X G hX ih =>
      intro hG
      rw [Finset.sup_insert]
      have hXF := hG (Finset.mem_insert_self X G)
      simp only [F, Finset.mem_filter] at hXF
      obtain ⟨R1, f1, h1⟩ := hXF.2
      obtain ⟨R2, f2, h2⟩ := ih ((Finset.subset_insert X G).trans hG)
      exact union_pm M R likes X R1 f1 h1 _ R2 f2 h2
  obtain ⟨Rs, fs, hs⟩ := hsup F subset_rfl
  have hall_sub : ∀ (M' : Finset α) (R' : Finset β) (g : α → β), IsProperMatch M R likes M' R' g →
      M' ⊆ F.sup id := by
    intro M' R' g h
    have : M' ∈ F := by
      simp only [F, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨h.1, R', g, h⟩
    exact Finset.le_sup (f := id) this
  refine ⟨F.sup id, hs.1, ?_, ⟨Rs, fs, hs⟩, hall_sub⟩
  by_contra hns
  -- the remaining graph
  have hcardS : (F.sup id).card = Rs.card := by
    have himg : Rs = (F.sup id).image fs := by
      apply Finset.coe_injective
      rw [Finset.coe_image]; exact hs.2.2.1.image_eq.symm
    rw [himg, Finset.card_image_of_injOn hs.2.2.1.injOn]
  have hc0 : (M \ F.sup id).card = (R \ Rs).card := by
    rw [Finset.card_sdiff_of_subset hs.1, Finset.card_sdiff_of_subset hs.2.1]
    omega
  have hi0 : istar ∈ M \ F.sup id := Finset.mem_sdiff.mpr ⟨hi, hns⟩
  obtain ⟨N, T, g, hpm, hiN⟩ := core (M \ F.sup id) (R \ Rs) likes hc0 istar hi0
    (fun r hr => hall r (Finset.mem_sdiff.mp hr).1) r0
  obtain ⟨hN, hT, hbij, hlk, hprop⟩ := hpm
  have hext := extend M R likes _ Rs fs hs N T g (hN.trans Finset.sdiff_subset)
    (fun a ha => (Finset.mem_sdiff.mp (hN ha)).2) (hT.trans Finset.sdiff_subset)
    (fun t ht => (Finset.mem_sdiff.mp (hT ht)).2) hbij hlk (by
      intro a ha t ht
      rw [Finset.mem_sdiff, Finset.mem_union, not_or] at ha
      exact hprop a (Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨ha.1, ha.2.1⟩, ha.2.2⟩) t ht)
  have := hall_sub _ _ _ hext
  exact hns (this (Finset.mem_union_right _ hiN))
