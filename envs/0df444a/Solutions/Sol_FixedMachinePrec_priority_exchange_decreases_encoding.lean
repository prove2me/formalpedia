-- Prove2me | solution 1 for FixedMachinePrec.priority_exchange_decreases_encoding
-- status  : ACCEPTED   (prove)
-- author  : @kj
-- created : 2026-11-26T17:05:56.633297+00:00
-- url     : https://prove2.me/submissions/71f94891-0095-4132-a523-37218089db02

import Definitions.Def_FixedMachinePrec_Separator

open FixedMachinePrec

-- If two sorted sets agree below a threshold and only the first contains the threshold,
-- their first difference decides the comparison regardless of the appended suffixes.
private theorem compare_rows (a b left right : List ℕ) (x y : ℕ) (xy : x < y)
    (sa : a.Pairwise (· ≤ ·)) (da : a.Nodup) (db : b.Nodup)
    (ax : x ∈ a) (bx : x ∉ b) (by' : y ∈ b) (same : ∀ z < x, z ∈ a ↔ z ∈ b) :
    a ++ left < b ++ right := by
  induction a generalizing b with
  | nil => contradiction
  | cons u a ih =>
    cases b with
    | nil => contradiction
    | cons v b =>
      have small : u ≤ x := by rcases List.mem_cons.mp ax with rfl|h; exact le_rfl; exact (List.pairwise_cons.mp sa).1 x h
      simp only [List.cons_append,List.cons_lt_cons_iff]
      rcases lt_trichotomy u v with h | rfl | h
      · exact Or.inl h
      · have ne : x ≠ u := by rintro rfl; simp at bx
        refine Or.inr ⟨rfl,ih _ (List.pairwise_cons.mp sa).2 (List.nodup_cons.mp da).2 (List.nodup_cons.mp db).2
          ((List.mem_cons.mp ax).resolve_left ne) (fun h => bx (by simp [h])) ?_ ?_⟩
        · exact (List.mem_cons.mp by').resolve_left (by omega)
        · intro z hz; by_cases ez : z=u
          · subst z; simp [(List.nodup_cons.mp da).1,(List.nodup_cons.mp db).1]
          · simpa [ez] using same z hz
      · have mem := (same v (by omega)).mpr (List.mem_cons_self ..)
        have tail := (List.mem_cons.mp mem).resolve_left (by omega)
        exact False.elim (h.not_ge ((List.pairwise_cons.mp sa).1 v tail))



private theorem union_mem {N} (s : List (Finset (Fin N))) (x) : x ∈ unionSlots s ↔ ∃ A ∈ s, x ∈ A := by
  unfold unionSlots; induction s with | nil => simp | cons A s ih => simp [ih]

private theorem slot_time {N} {s : List (Finset (Fin N))} (hd : s.Pairwise Disjoint) {i} (hi : i < s.length) {x} (hx : x ∈ s[i]) : localTime s x = i+1 := by
  unfold localTime
  congr 1
  apply (List.findIdx_eq hi).mpr
  refine ⟨decide_eq_true hx,?_⟩
  intro j hj; simp only [decide_eq_false_iff_not]
  exact fun h => Finset.disjoint_left.mp (List.pairwise_iff_getElem.mp hd j i (hj.trans hi) hi hj) h hx


theorem solution {N : ℕ} (m : ℕ) (prec : Fin N → Fin N → Prop) [DecidableRel prec] (U : Finset (Fin N)) (pri : List (Fin N)) (hp : IsPriorityList prec U pri)
    (Zs ρ : List (Finset (Fin N))) (hZ : IsFullSchedule prec m U Zs) (hρ : IsFullSchedule prec m U ρ)
    (r : ℕ) (hr : 1 ≤ r) (hb : r ≤ Zs.length) (he : ρ.take r = Zs.take r)
    (x y : Fin N) (hy : y ∈ ρ.getD (r-1) ∅) (hx : x ∈ U) (hl : r < localTime ρ x)
    (hprio : pri.idxOf x < pri.idxOf y) : priEnc pri (swapJobs ρ x y) < priEnc pri Zs := by
  classical
  have hrρ : r ≤ ρ.length := by
    have e := congrArg List.length he
    simp only [List.length_take,Nat.min_eq_left hb] at e
    omega
  let i := r-1
  have hi : i < ρ.length := by dsimp [i];omega
  have ir : i+1 = r := by dsimp [i];omega
  let P := ρ.take i
  let A := ρ[i]
  let key := fun z : Fin N => pri.idxOf z + 1
  let row := fun B : Finset (Fin N) => (B.image key).sort (· ≤ ·)
  let swap := fun B : Finset (Fin N) => B.image (Equiv.swap x y)
  have ay : y ∈ A := by simpa [List.getD_eq_getElem?_getD,show r-1 < ρ.length from hi,A,i] using hy
  have ax : x ∉ A := by intro h; have e := slot_time hρ.2.1 hi h; omega
  have split' : ρ.take r = P ++ [A] := ir ▸ List.take_succ_eq_append_getElem hi
  have decomp : ρ = P ++ A :: ρ.drop r := by rw [← List.singleton_append,← List.append_assoc,← split',List.take_append_drop]
  have decomp' : Zs = P ++ A :: Zs.drop r := by rw [← List.singleton_append,← List.append_assoc,← split',he,List.take_append_drop]
  have fresh (B : Finset (Fin N)) (h : B ∈ P) : x ∉ B ∧ y ∉ B := by
    obtain ⟨j,hj,hB⟩ := List.mem_iff_getElem.mp h
    have hlt : j < i := by
      have e : j < min i ρ.length := by simpa [P] using hj
      omega
    have hj' := hlt.trans hi
    have eq : ρ[j] = B := by simpa [P] using hB
    rw [← eq]
    constructor
    · intro h; have ht := slot_time hρ.2.1 hj' h;omega
    · exact fun h => Finset.disjoint_left.mp (List.pairwise_iff_getElem.mp hρ.2.1 j i hj' hi hlt) h ay
  have fixed : P.map swap = P := by
    conv_rhs => rw [← List.map_id P]
    apply List.map_congr_left
    intro B hB
    change B.image (Equiv.swap x y) = B
    have := fresh B hB
    convert (Finset.image_id (s := B)) using 1
    apply Finset.image_congr; intro z hz
    exact Equiv.swap_apply_of_ne_of_ne (by rintro rfl;tauto) (by rintro rfl;tauto)
  have inU {z} (hz : z ∈ A) : z ∈ U := hρ.2.2.1 ▸ (union_mem _ _).mpr ⟨A,List.getElem_mem hi,hz⟩
  have kinj {u v : Fin N} (hu : u ∈ U) (hv : v ∈ U) (eq : key u = key v) : u=v := by
    have pu := List.mem_toFinset.mp (hp.2.1 ▸ hu)
    have pv := List.mem_toFinset.mp (hp.2.1 ▸ hv)
    have e : pri.idxOf u = pri.idxOf v := by simpa [key] using eq
    have a := List.getElem_idxOf (List.idxOf_lt_length_of_mem pu)
    simp only [e] at a; exact a.symm.trans (List.getElem_idxOf (List.idxOf_lt_length_of_mem pv))
  have kxy : key x < key y := Nat.succ_lt_succ hprio
  have rowmem (B) (z) : z ∈ row B ↔ ∃ w ∈ B, key w = z := by simp [row]
  have yes : key x ∈ row (swap A) := (rowmem ..).mpr ⟨x,Finset.mem_image.mpr ⟨y,ay,Equiv.swap_apply_right ..⟩,rfl⟩
  have no : key x ∉ row A := by
    intro h; obtain ⟨w,hw,e⟩ := (rowmem ..).mp h
    exact ax (kinj (inU hw) hx e ▸ hw)
  have same (z) (hz : z < key x) : z ∈ row (swap A) ↔ z ∈ row A := by
    simp only [rowmem,swap,Finset.mem_image]
    constructor
    · rintro ⟨_,⟨w,hw,rfl⟩,e⟩
      by_cases wy : w=y
      · subst w; simp at e;omega
      · rw [Equiv.swap_apply_of_ne_of_ne (show w ≠ x from fun eq => ax (eq ▸ hw)) wy] at e
        exact ⟨w,hw,e⟩
    · rintro ⟨w,hw,e⟩
      have wy : w ≠ y := by rintro rfl;omega
      exact ⟨w,⟨w,hw,Equiv.swap_apply_of_ne_of_ne (fun eq => ax (eq ▸ hw)) wy⟩,e⟩
  change ((ρ.map swap).flatMap row) < Zs.flatMap row
  conv_lhs => rw [decomp]
  conv_rhs => rw [decomp']
  simp only [List.map_append,List.map_cons,fixed,List.flatMap_append,List.flatMap_cons]
  apply List.append_left_lt
  exact compare_rows _ _ _ _ _ _ kxy (Finset.pairwise_sort ..) (Finset.sort_nodup ..) (Finset.sort_nodup ..) yes no ((rowmem ..).mpr ⟨y,ay,rfl⟩) same
