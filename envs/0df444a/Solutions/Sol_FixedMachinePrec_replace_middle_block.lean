-- Prove2me | solution 1 for FixedMachinePrec.replace_middle_block
-- status  : ACCEPTED   (prove)
-- author  : @kj
-- created : 2026-11-26T17:04:11.795196+00:00
-- url     : https://prove2.me/submissions/42f0f7be-bcc5-40d7-8b4c-42e3d52e7952

import Definitions.Def_FixedMachinePrec_Separator

open FixedMachinePrec

private def beforeSlot {N} (p : Fin N → Fin N → Prop) (a b : Finset (Fin N)) :=
  Disjoint a b ∧ ∀ x ∈ a, ∀ y ∈ b, ¬p y x

private theorem full_iff {N m} {p : Fin N → Fin N → Prop} {W S} : IsFullSchedule p m W S ↔
    (∀ a ∈ S, a.card = m ∧ IsAntichainSet p a) ∧ S.Pairwise (beforeSlot p) ∧ unionSlots S = W := by
  constructor
  · rintro ⟨hslots,hd,hu,ho⟩
    refine ⟨hslots,List.pairwise_iff_getElem.mpr ?_,hu⟩
    intro i j hi hj hij
    exact ⟨List.pairwise_iff_getElem.mp hd i j hi hj hij,fun x hx y hy hp => hij.asymm (ho j i hj hi y x hy hx hp)⟩
  · rintro ⟨hslots,hw,hu⟩
    refine ⟨hslots,hw.imp (fun h => h.1),hu,?_⟩
    intro i j hi hj x y hx hy hxy
    by_contra! rev
    rcases rev.eq_or_lt with e | e
    · subst j; exact (hslots _ (List.getElem_mem hi)).2 _ hx _ hy hxy
    · exact (List.pairwise_iff_getElem.mp hw j i hj hi e).2 y hy x hx hxy

private theorem union_mem {N} (S : List (Finset (Fin N))) (x) : x ∈ unionSlots S ↔ ∃ a ∈ S, x ∈ a := by
  unfold unionSlots; induction S with | nil => simp | cons a s ih => simp [ih]

private theorem transfer_right {N} {p : Fin N → Fin N → Prop} {a b : Finset (Fin N)} {L : List (Finset (Fin N))}
    (h : ∀ c ∈ L, beforeSlot p a c) (hb : b ⊆ unionSlots L) : beforeSlot p a b := by
  refine ⟨Finset.disjoint_left.mpr ?_,?_⟩
  · intro x hx hy; obtain ⟨c,hc,hxc⟩ := (union_mem L x).mp (hb hy); exact Finset.disjoint_left.mp (h c hc).1 hx hxc
  · intro x hx y hy; obtain ⟨c,hc,hyc⟩ := (union_mem L y).mp (hb hy); exact (h c hc).2 x hx y hyc

private theorem transfer_left {N} {p : Fin N → Fin N → Prop} {a b : Finset (Fin N)} {L : List (Finset (Fin N))}
    (h : ∀ c ∈ L, beforeSlot p c b) (ha : a ⊆ unionSlots L) : beforeSlot p a b := by
  refine ⟨Finset.disjoint_left.mpr ?_,?_⟩
  · intro x hx hy; obtain ⟨c,hc,hxc⟩ := (union_mem L x).mp (ha hx); exact Finset.disjoint_left.mp (h c hc).1 hxc hy
  · intro x hx y hy; obtain ⟨c,hc,hxc⟩ := (union_mem L x).mp (ha hx); exact (h c hc).2 x hxc y hy

theorem solution {N : ℕ} (m : ℕ) (prec : Fin N → Fin N → Prop) [DecidableRel prec] (W U : Finset (Fin N)) (L A R B : List (Finset (Fin N)))
    (h : IsFullSchedule prec m W (L ++ A ++ R)) (hu : unionSlots A = U) (hb : IsFullSchedule prec m U B) : IsFullSchedule prec m W (L ++ B ++ R) := by
  obtain ⟨good,order,cover⟩ := full_iff.mp h
  obtain ⟨goodB,orderB,coverB⟩ := full_iff.mp hb
  have sub (b) (h : b ∈ B) : b ⊆ unionSlots A := by intro x hx; rw [hu,← coverB]; exact (union_mem B x).mpr ⟨b,h,hx⟩
  obtain ⟨ordLA,ordR,cross⟩ := List.pairwise_append.mp order
  obtain ⟨ordL,_,la⟩ := List.pairwise_append.mp ordLA
  apply full_iff.mpr; refine ⟨?_,?_,?_⟩
  · intro b h; simp only [List.mem_append] at h; rcases h with (h|h)|h
    · exact good b (by simp [h])
    · exact goodB b h
    · exact good b (by simp [h])
  · apply List.pairwise_append.mpr
    refine ⟨List.pairwise_append.mpr ⟨ordL,orderB,fun x hx y hy => transfer_right (la x hx) (sub y hy)⟩,ordR,?_⟩
    intro x hx y hy
    rcases List.mem_append.mp hx with hx|hx
    · exact cross x (by simp [hx]) y hy
    · exact transfer_left (fun c hc => cross c (by simp [hc]) y hy) (sub x hx)
  · have union_app (l s : List (Finset (Fin N))) : unionSlots (l++s) = unionSlots l ∪ unionSlots s := by
      ext x; simp only [union_mem,Finset.mem_union,List.mem_append]; grind
    simpa [union_app,coverB,hu] using cover
