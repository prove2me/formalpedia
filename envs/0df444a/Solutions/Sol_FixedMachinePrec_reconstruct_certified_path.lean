-- Prove2me | solution 1 for FixedMachinePrec.reconstruct_certified_path
-- status  : ACCEPTED   (prove)
-- author  : @kj
-- created : 2026-11-26T16:56:05.39541+00:00
-- url     : https://prove2.me/submissions/9de18176-67d7-42a1-a766-37428447118b

import Definitions.Def_FixedMachinePrec_EvaluateFamily

open FixedMachinePrec

private theorem member_union {N : ℕ} {S : List (Finset (Fin N))} {A} (ha : A ∈ S) : A ⊆ S.foldr (· ∪ ·) ∅ := by
  induction S with
  | nil => contradiction
  | cons B S ih => rcases List.mem_cons.mp ha with rfl | h; exact Finset.subset_union_left; exact (ih h).trans Finset.subset_union_right

private theorem append_full {N m : ℕ} {p : Fin N → Fin N → Prop} {A B : Finset (Fin N)} {S T}
    (hs : IsFullSchedule p m A S) (ht : IsFullSchedule p m B T) (hd : Disjoint A B)
    (hcross : ∀ x ∈ B, ∀ y ∈ A, ¬p x y) : IsFullSchedule p m (A ∪ B) (S ++ T) := by
  obtain ⟨sa,sd,su,sp⟩ := hs
  obtain ⟨ta,td,tu,tp⟩ := ht
  have hA {a} (h : a ∈ S) : a ⊆ A := su ▸ member_union h
  have hB {a} (h : a ∈ T) : a ⊆ B := tu ▸ member_union h
  refine ⟨fun a ha => (List.mem_append.mp ha).elim (sa a) (ta a),List.pairwise_append.mpr ⟨sd,td,fun a ha b hb => hd.mono (hA ha) (hB hb)⟩,?_,?_⟩
  · rw [List.foldr_append, tu, ← su]; clear * - S B
    induction S with | nil => simp | cons a l ih => simp [ih,Finset.union_assoc]
  · intro i j hi hj x y hx hy hp
    by_cases li : i < S.length <;> by_cases lj : j < S.length
    · rw [List.getElem_append_left li] at hx; rw [List.getElem_append_left lj] at hy
      exact sp _ _ li lj x y hx hy hp
    · omega
    · rw [List.getElem_append_right (by omega)] at hx; rw [List.getElem_append_left lj] at hy
      exact False.elim (hcross x (hB (List.getElem_mem _) hx) y (hA (List.getElem_mem _) hy) hp)
    · rw [List.getElem_append_right (by omega)] at hx hy
      have := tp _ _ (by simpa [List.length_append] using (show i - S.length < T.length by simp only [List.length_append] at hi;omega)) (by simp only [List.length_append] at hj;omega) x y hx hy hp
      omega

private theorem glue {N m : ℕ} {p : Fin N → Fin N → Prop} {W A B C : Finset (Fin N)} {S T}
    (ha : A ⊆ B) (hb : B ⊆ C) (hc : C ⊆ W) (ideal : IsIdealIn p W B)
    (hs : IsFullSchedule p m (B \ A) S) (ht : IsFullSchedule p m (C \ B) T) : IsFullSchedule p m (C \ A) (S ++ T) := by
  have h := append_full hs ht (by rw [Finset.disjoint_left];intro x hx hy; exact (Finset.mem_sdiff.mp hy).2 (Finset.mem_sdiff.mp hx).1) (by
    intro x hx y hy hp
    exact (Finset.mem_sdiff.mp hx).2 (ideal.2 y (Finset.mem_sdiff.mp hy).1 x (hc (Finset.mem_sdiff.mp hx).1) hp))
  convert h using 1
  ext z; simp only [Finset.mem_sdiff, Finset.mem_union]; have := @ha z; have := @hb z; tauto

private theorem record_spec {N m} (p : Fin N → Fin N → Prop) [DecidableRel p] (C W) (a) (ha : a ∈ buildStates p m C W) :
    IsIdealIn p W a.L ∧ IsIdealIn p W (a.L ∪ a.Z) ∧ (a.L ∪ a.Z) \ a.L = a.Z ∧
    a.R = W \ (a.L ∪ a.Z) ∧ IsFullSchedule p m a.Z [a.Z] := by
  obtain ⟨cut,_,h⟩ := List.mem_flatMap.mp ha
  dsimp only at h
  split at h
  · obtain ⟨Z,hZ,he⟩ := List.mem_filterMap.mp h
    obtain ⟨hset,hsub⟩ := List.mem_filter.mp hZ
    simp only [decide_eq_true_eq] at hsub
    obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hset
    obtain ⟨hl,hlen⟩ := List.mem_sublistsLen.mp (List.mem_mergeSort.mp hl)
    have hcard := (List.toFinset_card_of_nodup ((List.nodup_finRange N).sublist hl)).trans hlen
    split at he
    · rename_i good
      cases he
      obtain ⟨_,anti,il,iz⟩ := good
      have sub : W ∩ cut ∪ l.toFinset ⊆ W := Finset.union_subset Finset.inter_subset_left (hsub.trans Finset.sdiff_subset)
      refine ⟨⟨Finset.inter_subset_left,il⟩,⟨sub,iz⟩,?_,rfl,?_⟩
      · ext x; simp only [Finset.mem_sdiff,Finset.mem_union]; have := fun (hx : x ∈ l.toFinset) => (Finset.mem_sdiff.mp (hsub hx)).2; tauto
      · refine ⟨by simpa using And.intro hcard anti,by simp,by simp,?_⟩
        intro i j hi hj x y hx hy hp
        simp only [List.length_singleton] at hi hj
        obtain rfl : i = 0 := by omega
        obtain rfl : j = 0 := by omega
        exact False.elim (anti x hx y hy hp)
    · contradiction
  · contradiction

theorem solution {N : ℕ} (m : ℕ) (prec : Fin N → Fin N → Prop) [DecidableRel prec] (_hm : 1 ≤ m) (F C : Finset (Finset (Fin N))) (W : Finset (Fin N)) (tab : Table N)
    (hs : ∀ X S, tab X = some S → IsFullSchedule prec m X S) (p : ℕ → PredField) (t : ℕ) :
    let st := buildStates prec m C W
    let lk := fun X => (lookup F tab X).isSome
    let path := tracePath p st.length t
    (∃ a, st[t]? = some a ∧ lk a.R = true) →
    (∃ i rest, path = i :: rest ∧ (∃ a, st[i]? = some a ∧ lk a.L = true) ∧
      path.getLast? = some t ∧ path.IsChain (fun i j => edge st lk i j = true)) →
    IsFullSchedule prec m W (reconstruct st (fun X => (lookup F tab X).getD []) p t) := by
  let st := buildStates prec m C W
  let lk := fun X => (lookup F tab X).isSome
  let fetch := fun X => (lookup F tab X).getD []
  have sound (X) (h : lk X = true) : IsFullSchedule prec m X (fetch X) := by
    obtain ⟨s,he⟩ := Option.isSome_iff_exists.mp h
    have hh : tab X = some s := by unfold lookup at he; split at he <;> simp_all
    simpa [fetch,he] using hs X s hh
  dsimp only
  intro last cert
  obtain ⟨i,rest,ep,⟨a,ha,hinit⟩,hl,hchain⟩ := cert
  rw [ep] at hl hchain
  have suffix (l : List ℕ) (i : ℕ) (a : StateRec N) (hi : st[i]? = some a) (hl : (i::l).getLast? = some t)
      (he : (i::l).IsChain (fun i j => edge st lk i j = true)) :
      IsFullSchedule prec m (W \ a.L) (assemble st fetch (i::l)) := by
    induction l generalizing i a with
    | nil =>
      have eit : i = t := by simpa using hl
      subst i
      obtain ⟨b,hb,hR⟩ := last
      have eb : b = a := Option.some.inj (hb.symm.trans hi); subst b
      obtain ⟨_,ideal,heq,hrest,hslot⟩ := record_spec prec C W a (List.mem_of_getElem? hi)
      rw [assemble,hi]
      apply glue (B := a.L ∪ a.Z) Finset.subset_union_left ideal.1 (by rfl) ideal (by rw [heq]; exact hslot)
      exact hrest ▸ sound _ hR
    | cons j rest ih =>
      obtain ⟨hij,htail⟩ := List.isChain_cons_cons.mp he
      change edge st lk i j = true at hij
      unfold edge at hij
      rw [hi] at hij
      split at hij
      · rename_i aa b haa hb
        cases haa
        obtain ⟨hsub,hgap⟩ := Bool.and_eq_true_iff.mp hij
        have sub := of_decide_eq_true hsub
        obtain ⟨_,ia,eqz,_,slot⟩ := record_spec prec C W a (List.mem_of_getElem? hi)
        have ib := (record_spec prec C W b (List.mem_of_getElem? hb)).1
        have seg := glue (p := prec) (W := W) Finset.subset_union_left sub ib.1 ia (by rw [eqz]; exact slot) (sound _ hgap)
        have tail := ih j b hb (by simpa using hl) htail
        simpa only [assemble,hi,hb] using glue (A := a.L) (Finset.subset_union_left.trans sub) ib.1 (by rfl) ib seg tail
      · contradiction
  have suf := suffix rest i a ha hl hchain
  have ia := (record_spec prec C W a (List.mem_of_getElem? ha)).1
  have whole := glue (A := ∅) (B := a.L) (C := W) (Finset.empty_subset _) ia.1 (by rfl) ia (by simpa using sound _ hinit) suf
  change IsFullSchedule prec m W (reconstruct st fetch p t)
  unfold reconstruct
  change tracePath p st.length t = i :: rest at ep
  change st[i]? = some a at ha
  simp only [ep,ha]; simpa using whole
