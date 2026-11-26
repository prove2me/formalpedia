-- Prove2me | solution 1 for FixedMachinePrec.lemma_7_3
-- status  : ACCEPTED   (prove)
-- author  : @kj
-- created : 2026-11-26T17:01:04.666485+00:00
-- url     : https://prove2.me/submissions/b1f5e47a-ce53-4698-a3d9-23f99f006fbd

import Definitions.Def_FixedMachinePrec_Separator

open FixedMachinePrec

private theorem union_mem {N} (s : List (Finset (Fin N))) (x) : x ∈ unionSlots s ↔ ∃ A ∈ s, x ∈ A := by
  unfold unionSlots; induction s with | nil => simp | cons A s ih => simp [ih]

private theorem slot_time {N} {s : List (Finset (Fin N))} (hd : s.Pairwise Disjoint) {i} (hi : i < s.length) {x} (hx : x ∈ s[i]) : localTime s x = i+1 := by
  unfold localTime
  congr 1
  apply (List.findIdx_eq hi).mpr
  refine ⟨decide_eq_true hx,?_⟩
  intro j hj; simp only [decide_eq_false_iff_not]
  exact fun h => Finset.disjoint_left.mp (List.pairwise_iff_getElem.mp hd j i (hj.trans hi) hi hj) h hx

private theorem location {N} {s : List (Finset (Fin N))} {x} (hx : x ∈ unionSlots s) :
    ∃ (i : ℕ) (hi : i < s.length), x ∈ s[i] := by
  obtain ⟨A,hA,hx⟩ := (union_mem _ _).mp hx
  obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hA
  exact ⟨i,hi,hx⟩

private theorem prefix_time {N} {s : List (Finset (Fin N))} (hd : s.Pairwise Disjoint) (r x) :
    x ∈ slotsBetween s 0 r ↔ x ∈ unionSlots s ∧ localTime s x < r := by
  simp only [slotsBetween,Finset.mem_biUnion,Finset.mem_filter,Finset.mem_range]
  constructor
  · rintro ⟨i,⟨hi,_,hlt⟩,hx⟩
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi] at hx
    exact ⟨(union_mem _ _).mpr ⟨_,List.getElem_mem hi,hx⟩,slot_time hd hi hx ▸ hlt⟩
  · rintro ⟨hu,ht⟩; obtain ⟨i,hi,hx⟩ := location hu
    exact ⟨i,⟨hi,by omega,slot_time hd hi hx ▸ ht⟩,by simpa [List.getD_eq_getElem?_getD,hi] using hx⟩

private theorem reversed_time {N} {s : List (Finset (Fin N))} (hd : s.Pairwise Disjoint) {x} (hx : x ∈ unionSlots s) :
    localTime s.reverse x + localTime s x = s.length + 1 := by
  obtain ⟨i,hi,hx⟩ := location hx
  have hr : s.reverse.Pairwise Disjoint := List.pairwise_reverse.mpr (hd.imp fun h => h.symm)
  have hj : s.length-1-i < s.reverse.length := by simp;omega
  have he : s.length-1-(s.length-1-i) = i := by omega
  have hy : x ∈ s.reverse[s.length-1-i] := by simpa only [List.getElem_reverse,he] using hx
  rw [slot_time hr hj hy,slot_time hd hi hx]; omega

theorem solution {N : ℕ} (m : ℕ) (_hm : 3 ≤ m) (prec : Fin N → Fin N → Prop) [DecidableRel prec]
    (hprec : IsStrictOrder' prec) (U : Finset (Fin N)) (Zs : List (Finset (Fin N)))
    (hZs : IsFullSchedule prec m U Zs) (_hne : Zs ≠ []) (S H : Finset (Fin N)) (r : ℕ)
    (hsep : Separates prec Zs S r) (hH : H ∩ U = S) :
    slotsBetween Zs 0 r = U ∩ sepFormula prec (Zs.getD (r - 1) ∅) H ∧
    Separates (fun x y => prec y x) Zs.reverse (U \ S) (Zs.length + 1 - r) ∧
    (IsIdealIn prec Finset.univ H → IsIdealIn prec Finset.univ (sepFormula prec (Zs.getD (r - 1) ∅) H)) := by
  let z := Zs.getD (r-1) ∅
  have hu : unionSlots Zs = U := hZs.2.2.1
  obtain ⟨ideal,rpos,rle,early,late⟩ := hsep
  have idx : r-1 < Zs.length := by omega
  have zr : z = Zs[r-1] := by simp [z,List.getD_eq_getElem?_getD,idx]
  have dep {x y} (hx : x ∈ U) (hy : y ∈ U) (hp : prec x y) : localTime Zs x < localTime Zs y := by
    obtain ⟨i,hi,hxi⟩ := location (hu ▸ hx)
    obtain ⟨j,hj,hyj⟩ := location (hu ▸ hy)
    rw [slot_time hZs.2.1 hi hxi,slot_time hZs.2.1 hj hyj]
    exact Nat.succ_lt_succ (hZs.2.2.2 i j hi hj x y hxi hyj hp)
  have inz {x} (hx : x ∈ z) : x ∈ U := hu ▸ (union_mem _ _).mpr ⟨_,List.getElem_mem idx,zr ▸ hx⟩
  have timez {x} (hx : x ∈ z) : localTime Zs x = r := (slot_time hZs.2.1 idx (zr ▸ hx)).trans (by omega)
  have zp {x} (hx : x ∈ U) (hp : x ∈ predCone prec z) : localTime Zs x < r := by
    obtain ⟨a,ha,hh⟩ := (Finset.mem_filter.mp hp).2
    exact timez ha ▸ dep hx (inz ha) hh
  have zd {x} (hx : x ∈ U) (hp : x ∈ succCone prec z) : r < localTime Zs x := by
    obtain ⟨a,ha,hh⟩ := (Finset.mem_filter.mp hp).2
    exact timez ha ▸ dep (inz ha) hx hh
  refine ⟨?_,?_,?_⟩
  · ext x
    rw [prefix_time hZs.2.1,hu,Finset.mem_inter]
    change _ ↔ x ∈ U ∧ (x ∈ predCone prec z ∪ (H \ weakSuccCone prec z))
    simp only [weakSuccCone,Finset.mem_union,Finset.mem_sdiff]
    constructor
    · rintro ⟨hx,ht⟩; refine ⟨hx,?_⟩
      by_cases hs : x ∈ S
      · right; refine ⟨(Finset.mem_inter.mp (hH ▸ hs)).1,?_⟩
        rintro (hd|hz); exact (zd hx hd).asymm ht; exact ht.ne (timez hz)
      · exact Or.inl (early x (Finset.mem_sdiff.mpr ⟨hu ▸ hx,hs⟩) ht)
    · rintro ⟨hx,h⟩; refine ⟨hx,?_⟩
      rcases h with hp | ⟨hh,hn⟩
      · exact zp hx hp
      · by_contra! ht
        rcases ht.eq_or_lt with he | hl
        · obtain ⟨i,hi,hxi⟩ := location (hu ▸ hx)
          have htm := slot_time hZs.2.1 hi hxi
          obtain e : i = r-1 := by omega
          subst i; exact hn (Or.inr (zr ▸ hxi))
        · exact hn (Or.inl (late x (hH ▸ Finset.mem_inter.mpr ⟨hh,hx⟩) hl))
  · have ur : unionSlots Zs.reverse = U := by ext x; simp only [← hu,union_mem,List.mem_reverse]
    have hidx : Zs.length+1-r-1 < Zs.reverse.length := by simp;omega
    have same : Zs.reverse.getD (Zs.length+1-r-1) ∅ = z := by
      simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hidx,Option.getD_some,List.getElem_reverse,zr]
      congr 1 <;> omega
    unfold Separates; rw [ur,same]
    refine ⟨⟨Finset.sdiff_subset,?_⟩,by omega,by simp;omega,?_,?_⟩
    · intro y hy x hx hp
      exact Finset.mem_sdiff.mpr ⟨hx,fun hs => (Finset.mem_sdiff.mp hy).2 (ideal.2 x hs y (hu ▸ (Finset.mem_sdiff.mp hy).1) hp)⟩
    · intro x hx ht
      obtain ⟨hx,hn⟩ := Finset.mem_sdiff.mp hx
      have hs : x ∈ S := by by_contra h; exact hn (Finset.mem_sdiff.mpr ⟨hx,h⟩)
      have := reversed_time hZs.2.1 (hu ▸ hx)
      exact late x hs (by omega)
    · intro x hx ht
      have := reversed_time hZs.2.1 (hu ▸ (Finset.mem_sdiff.mp hx).1)
      exact early x (hu ▸ hx) (by omega)
  · intro hI; refine ⟨Finset.subset_univ _,?_⟩
    intro y hy x hx hxy
    rcases Finset.mem_union.mp hy with hp | hh
    · obtain ⟨a,ha,hh⟩ := (Finset.mem_filter.mp hp).2
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx,a,ha,hprec.2 _ _ _ hxy hh⟩)
    · obtain ⟨hy,hnot⟩ := Finset.mem_sdiff.mp hh
      apply Finset.mem_union_right _; apply Finset.mem_sdiff.mpr
      refine ⟨hI.2 y hy x hx hxy,?_⟩
      intro bad
      apply hnot; apply Finset.mem_union_left _; apply Finset.mem_filter.mpr
      rcases Finset.mem_union.mp bad with h | h
      · obtain ⟨a,ha,hax⟩ := (Finset.mem_filter.mp h).2
        exact ⟨Finset.mem_univ _,a,ha,hprec.2 _ _ _ hax hxy⟩
      · exact ⟨Finset.mem_univ _,x,h,hxy⟩
