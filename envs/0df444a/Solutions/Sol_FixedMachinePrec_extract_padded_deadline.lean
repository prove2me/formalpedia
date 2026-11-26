-- Prove2me | solution 1 for FixedMachinePrec.extract_padded_deadline
-- status  : ACCEPTED   (prove)
-- author  : @kj
-- created : 2026-11-26T12:27:36.757828+00:00
-- url     : https://prove2.me/submissions/457eb535-e813-4dbf-b059-c89f0b530687

import Definitions.Def_FixedMachinePrec_Deadline

open FixedMachinePrec

private theorem mem_union_slots {α : Type*} [DecidableEq α] (x : α) (l : List (Finset α)) :
    x ∈ l.foldr (· ∪ ·) ∅ ↔ ∃ A ∈ l, x ∈ A := by
  induction l with
  | nil => simp
  | cons A l ih => simp [ih]

theorem solution (G : Instance) (m T : ℕ) (hsize : G.n ≤ m*T) (S : List (Finset (Fin (m*T))))
    (h : IsFullSchedule (paddedPrec G (m*T)) m Finset.univ S) (hlen : S.length = T) :
    (extractSchedule G S).MeetsDeadline m T := by
  classical
  let orig (x : Fin G.n) : Fin (m*T) := Fin.castLE hsize x
  let idx (x : Fin G.n) := S.findIdx (fun A => decide (x.val ∈ A.image Fin.val))
  have occurs (x : Fin G.n) : ∃ A ∈ S, decide (x.val ∈ A.image Fin.val) = true := by
    have hu : orig x ∈ S.foldr (· ∪ ·) ∅ := h.2.2.1 ▸ Finset.mem_univ _
    obtain ⟨A,hA,hx⟩ := (mem_union_slots _ _).mp hu
    exact ⟨A,hA,decide_eq_true (Finset.mem_image.mpr ⟨orig x,hx,rfl⟩)⟩
  have bound (x) : idx x < S.length := List.findIdx_lt_length_of_exists (occurs x)
  let A (x : Fin G.n) := S.getD (idx x) ∅
  have row (x) : A x = S[idx x]'(bound x) := by simp [A,List.getD_eq_getElem?_getD,bound x]
  have inside (x) : orig x ∈ A x := by
    have hit : decide (x.val ∈ (S[idx x]'(bound x)).image Fin.val) = true := List.findIdx_getElem (xs := S) (p := fun B => decide (x.val ∈ B.image Fin.val)) (w := bound x)
    obtain ⟨y,hy,he⟩ := Finset.mem_image.mp (of_decide_eq_true hit)
    rw [row]; exact (Fin.ext he : y = orig x) ▸ hy
  let earlier (x : Fin G.n) := (A x).filter (fun y => y.val < G.n ∧ y.val < x.val)
  have machineBound (x) : (earlier x).card < m := by
    have hm := (h.1 (A x) (by rw [row]; apply List.getElem_mem)).1
    apply lt_of_lt_of_eq _ hm
    apply Finset.card_lt_card
    apply (Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)).mpr
    exact ⟨orig x,inside x, by simp [orig]⟩
  have ordered (x y : Fin G.n) (ht : idx x = idx y) (hlt : x.val < y.val) :
      (earlier x).card < (earlier y).card := by
    have eA : A x = A y := congrArg (fun i => S.getD i ∅) ht
    apply Finset.card_lt_card
    apply (Finset.ssubset_iff_of_subset ?_).mpr
    · refine ⟨orig x, Finset.mem_filter.mpr ⟨eA ▸ inside x,x.isLt,hlt⟩,?_⟩
      simp [earlier,orig]
    · intro z hz
      obtain ⟨hz,hn,hlt'⟩ := Finset.mem_filter.mp hz
      exact Finset.mem_filter.mpr ⟨eA ▸ hz,hn,hlt'.trans hlt⟩
  let σ : Schedule G m := ⟨fun x => idx x, fun x => ⟨(earlier x).card,machineBound x⟩⟩
  refine ⟨σ,?_,?_,?_⟩
  · intro x
    change (idx x : ℝ) = ((idx x+1 : ℕ) : ℝ)-1 ∧ (earlier x).card = (earlier x).card
    simp
  · refine ⟨fun x => Nat.cast_nonneg _,?_,?_⟩
    · intro x y hne hmach
      have hxy : idx x ≠ idx y := by
        intro eq
        have em : (earlier x).card = (earlier y).card := congrArg Fin.val hmach
        rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with lt | gt
        · exact (ordered x y eq lt).ne em
        · exact (ordered y x eq.symm gt).ne em.symm
      rcases lt_or_gt_of_ne hxy with lt | gt
      · left; change (idx x : ℝ)+1 ≤ idx y; exact_mod_cast lt
      · right; change (idx y : ℝ)+1 ≤ idx x; exact_mod_cast gt
    · intro x y hp
      have lt := h.2.2.2 _ _ (bound x) (bound y) (orig x) (orig y) (row x ▸ inside x) (row y ▸ inside y) ⟨x.isLt,y.isLt,hp⟩
      change (idx x : ℝ)+1 ≤ idx y; exact_mod_cast lt
  · unfold Schedule.cmax
    split
    · apply Finset.sup'_le
      intro x _
      have lt := bound x
      rw [hlen] at lt
      change (idx x : ℝ)+1 ≤ T; exact_mod_cast lt
    · positivity
