-- Prove2me | solution 1 for FixedMachinePrec.ideal_priority_extension
-- status  : ACCEPTED   (prove)
-- author  : @kj
-- created : 2026-11-26T17:03:35.248673+00:00
-- url     : https://prove2.me/submissions/68eb95ca-1196-43c8-81bb-000bf528e899

import Definitions.Def_FixedMachinePrec_Separator
import Definitions.Def_FixedMachinePrec_FixedOrders

open FixedMachinePrec


private theorem topo_complete {N : ℕ} (p : Fin N → Fin N → Prop) [DecidableRel p]
    (wf : WellFounded p) :
    let L := topoList p
    L.length = N ∧ (∀ x, x ∈ L) ∧ ∀ x y, p x y → L.idxOf x < L.idxOf y := by
  let Good (l : List (Fin N)) := l.Nodup ∧ ∀ y ∈ l, ∀ x, p x y → x ∈ l ∧ l.idxOf x < l.idxOf y
  let step (l : List (Fin N)) (_ : ℕ) := match (List.finRange N).find? (fun x => decide (x ∉ l ∧ ∀ y, p y x → y ∈ l)) with
    | some x => l ++ [x]
    | none => l
  have finish (xs : List ℕ) (l : List (Fin N)) (hl : Good l) (hn : l.length + xs.length = N) :
      let L := xs.foldl step l
      L.length = N ∧ (∀ x, x ∈ L) ∧ ∀ x y, p x y → L.idxOf x < L.idxOf y := by
    induction xs generalizing l with
    | nil =>
      have hc : l.toFinset = Finset.univ := by
        apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
        simp [List.toFinset_card_of_nodup hl.1] at hn ⊢; omega
      have allmem (x : Fin N) : x ∈ l := List.mem_toFinset.mp (hc ▸ Finset.mem_univ x)
      exact ⟨by simpa using hn, allmem,fun x y h => (hl.2 y (allmem y) x h).2⟩
    | cons a xs ih =>
      have missing : ∃ x : Fin N, x ∉ l := by
        by_contra! allmem
        have hc : l.toFinset = Finset.univ := Finset.eq_univ_of_forall (by simpa using allmem)
        have := congrArg Finset.card hc
        simp [List.toFinset_card_of_nodup hl.1] at this
        simp only [List.length_cons] at hn
        omega
      let rem : Set (Fin N) := {x | x ∉ l}
      have hrem : rem.Nonempty := missing
      let z := wf.min rem hrem
      have hz : z ∉ l := wf.min_mem rem hrem
      have hpred (y) (hy : p y z) : y ∈ l := by
        by_contra h
        exact wf.not_lt_min rem (show y ∈ rem from h) hy
      have hit : ((List.finRange N).find? (fun x => decide (x ∉ l ∧ ∀ y, p y x → y ∈ l))).isSome :=
        List.find?_isSome.mpr ⟨z,by simp,decide_eq_true ⟨hz,hpred⟩⟩
      obtain ⟨x,hx⟩ := Option.isSome_iff_exists.mp hit
      have hp : x ∉ l ∧ ∀ y, p y x → y ∈ l := of_decide_eq_true (List.find?_some (p := fun x => decide (x ∉ l ∧ ∀ y, p y x → y ∈ l)) hx)
      have hs : step l a = l ++ [x] := by dsimp only [step]; rw [hx]
      simp only [List.foldl_cons,hs]
      apply ih
      · constructor
        · simp [List.nodup_append, hl.1]; grind
        · intro y hy w hw
          rcases List.mem_append.mp hy with old | new
          · obtain ⟨hmem,hpos⟩ := hl.2 y old w hw
            simp [List.idxOf_append,old,hmem,hpos]
          · have eq : y = x := by simpa using new
            subst y
            have hmem := hp.2 w hw
            simp [List.idxOf_append,hp.1,hmem,List.idxOf_lt_length_of_mem hmem]
      · change (l ++ [x]).length + xs.length = N; simp at hn ⊢; omega
  exact finish (List.range N) [] (by simp [Good]) (by simp)

theorem solution {N : ℕ} (prec : Fin N → Fin N → Prop) (hp : IsStrictOrder' prec) (U I : Finset (Fin N))
    (hI : IsIdealIn prec U I) : ∃ pri : List (Fin N), IsPriorityList prec U pri ∧ priorityPrefix pri I.card = I := by
  classical
  letI : IsTrans _ prec := ⟨hp.2⟩
  letI : Std.Irrefl prec := ⟨hp.1⟩
  let L := topoList prec
  obtain ⟨hlen,hmem,horder⟩ := topo_complete prec (Finite.wellFounded_of_trans_of_irrefl prec)
  have eq : L.toFinset = Finset.univ := Finset.eq_univ_of_forall fun x => List.mem_toFinset.mpr (hmem x)
  have hd : L.Nodup := (Multiset.toFinset_card_eq_card_iff_nodup (m := (↑L : Multiset (Fin N)))).mp (show L.toFinset.card = L.length by rw [eq];simp [L,hlen])
  have sorted : L.Pairwise (fun x y => ¬prec y x) := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij hbad
    have h := horder _ _ hbad
    change L.idxOf L[j] < L.idxOf L[i] at h
    simp [hd.idxOf_getElem] at h
    omega
  let A := L.filter fun x => decide (x ∈ I)
  let B := L.filter fun x => decide (x ∈ U \ I)
  have setA : A.toFinset = I := by ext x; simp [A,L,hmem]
  have setB : B.toFinset = U \ I := by ext x; simp [B,L,hmem]
  have disj (x) (hx : x ∈ A) (hy : x ∈ B) : False := (Finset.mem_sdiff.mp (setB ▸ List.mem_toFinset.mpr hy)).2 (setA ▸ List.mem_toFinset.mpr hx)
  have hdA : A.Nodup := hd.filter _
  have hdB : B.Nodup := hd.filter _
  have hall : (A ++ B).toFinset = U := by rw [List.toFinset_append,setA,setB]; ext x; simp; have := @hI.1 x;tauto
  have hab : (A++B).Pairwise (fun x y => ¬prec y x) := by
    refine List.pairwise_append.mpr ⟨sorted.filter _,sorted.filter _,?_⟩
    intro x hx y hy h
    have hiy := Finset.mem_sdiff.mp (setB ▸ List.mem_toFinset.mpr hy)
    exact hiy.2 (hI.2 x (setA ▸ List.mem_toFinset.mpr hx) y hiy.1 h)
  refine ⟨A++B,⟨List.nodup_append.mpr ⟨hdA,hdB,by grind⟩,hall,?_⟩,?_⟩
  · intro x hx y hy hxy
    let P := A++B
    have hx' : x ∈ P := List.mem_toFinset.mp (hall ▸ hx)
    have hy' : y ∈ P := List.mem_toFinset.mp (hall ▸ hy)
    have ix := List.idxOf_lt_length_of_mem hx'
    have iy := List.idxOf_lt_length_of_mem hy'
    change P.idxOf x < P.idxOf y
    by_contra! rev
    rcases rev.eq_or_lt with e | e
    · have h : x = y := by
        have ex := List.getElem_idxOf ix
        simp only [← e] at ex
        exact ex.symm.trans (List.getElem_idxOf iy)
      exact hp.1 y (h ▸ hxy)
    · have h := List.pairwise_iff_getElem.mp hab _ _ iy ix e
      change ¬prec P[P.idxOf x] P[P.idxOf y] at h
      rw [List.getElem_idxOf,List.getElem_idxOf] at h
      exact h hxy
  · unfold priorityPrefix
    rw [← setA,List.toFinset_card_of_nodup hdA,List.take_left]
