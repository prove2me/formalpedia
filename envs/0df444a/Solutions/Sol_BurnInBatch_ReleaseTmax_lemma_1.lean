-- Prove2me | solution 1 for BurnInBatch.ReleaseTmax.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T02:06:00.829981+00:00
-- url     : https://prove2.me/submissions/9a85ac70-bac9-4a0c-a7c3-a2bfbe8017ca

import Mathlib
import Definitions.Def_BurnInBatch_ReleaseTmax_Model



namespace BurnInBatch.ReleaseTmax

open Classical

section Infra
variable {n : ℕ}

def stp (p : ℕ) (r : Fin n → ℕ) (t : ℕ) (P : Finset (Fin n)) : ℕ := max t (P.sup r) + p

theorem finish_cons (p : ℕ) (r : Fin n → ℕ) (P : Finset (Fin n)) (S : List (Finset (Fin n)))
    (t : ℕ) : finish p r (P :: S) t = finish p r S (stp p r t P) := rfl

theorem aux_cons (p : ℕ) (r : Fin n → ℕ) (j : Fin n) (P : Finset (Fin n))
    (S : List (Finset (Fin n))) (t : ℕ) :
    jobCompletionAux p r j (P :: S) t =
      if j ∈ P then stp p r t P else jobCompletionAux p r j S (stp p r t P) := rfl

def OT (p : ℕ) (r d : Fin n → ℕ) : List (Finset (Fin n)) → ℕ → Prop
  | [], _ => True
  | P :: S, t => (∀ j ∈ P, stp p r t P ≤ d j) ∧ OT p r d S (stp p r t P)

theorem le_stp (p : ℕ) (r : Fin n → ℕ) (t : ℕ) (P : Finset (Fin n)) : t + p ≤ stp p r t P :=
  Nat.add_le_add_right (le_max_left _ _) _

theorem stp_mono (p : ℕ) (r : Fin n → ℕ) {t t' : ℕ} (P : Finset (Fin n)) (h : t ≤ t') :
    stp p r t P ≤ stp p r t' P :=
  Nat.add_le_add_right (max_le_max h le_rfl) _

theorem finish_append (p : ℕ) (r : Fin n → ℕ) (S1 S2 : List (Finset (Fin n))) :
    ∀ t, finish p r (S1 ++ S2) t = finish p r S2 (finish p r S1 t) := by
  induction S1 with
  | nil => intro t; rfl
  | cons P S ih => intro t; simp only [List.cons_append, finish_cons]; exact ih _

theorem OT_append (p : ℕ) (r d : Fin n → ℕ) (S1 S2 : List (Finset (Fin n))) :
    ∀ t, OT p r d (S1 ++ S2) t ↔ OT p r d S1 t ∧ OT p r d S2 (finish p r S1 t) := by
  induction S1 with
  | nil => intro t; simp [OT, finish]
  | cons P S ih =>
    intro t
    simp only [List.cons_append, OT, finish_cons, ih]
    tauto

theorem OT_lt (p : ℕ) (r d : Fin n → ℕ) (S : List (Finset (Fin n))) :
    ∀ (t : ℕ) (u : Fin n), OT p r d S t → (∃ P ∈ S, u ∈ P) → t + p ≤ d u := by
  induction S with
  | nil => intro t u _ h; obtain ⟨P, hP, _⟩ := h; simp at hP
  | cons P S ih =>
    intro t u hO ⟨Q, hQ, hu⟩
    rcases List.mem_cons.mp hQ with rfl | hQ
    · exact (le_stp p r t Q).trans (hO.1 u hu)
    · have := ih (stp p r t P) u hO.2 ⟨Q, hQ, hu⟩
      exact (Nat.add_le_add_right (le_stp p r t P |>.trans' (Nat.le_add_right _ _)) _).trans this

theorem aux_le (p : ℕ) (r d : Fin n → ℕ) (S : List (Finset (Fin n))) :
    ∀ (t : ℕ) (u : Fin n), OT p r d S t → (∃ P ∈ S, u ∈ P) →
      jobCompletionAux p r u S t ≤ d u := by
  induction S with
  | nil => intro t u _ h; obtain ⟨P, hP, _⟩ := h; simp at hP
  | cons P S ih =>
    intro t u hO ⟨Q, hQ, hu⟩
    rw [aux_cons]
    split_ifs with h
    · exact hO.1 u h
    · apply ih _ u hO.2
      rcases List.mem_cons.mp hQ with rfl | hQ
      · exact absurd hu h
      · exact ⟨Q, hQ, hu⟩

theorem OT_of_aux (p : ℕ) (r d : Fin n → ℕ) (S : List (Finset (Fin n))) :
    ∀ (t : ℕ), S.Pairwise (fun P Q => Disjoint P Q) →
      (∀ u : Fin n, (∃ P ∈ S, u ∈ P) → jobCompletionAux p r u S t ≤ d u) → OT p r d S t := by
  induction S with
  | nil => intros; trivial
  | cons P S ih =>
    intro t hdis h
    rw [List.pairwise_cons] at hdis
    refine ⟨fun u hu => ?_, ih _ hdis.2 (fun u ⟨Q, hQ, hu⟩ => ?_)⟩
    · have := h u ⟨P, List.mem_cons_self, hu⟩
      rwa [aux_cons, if_pos hu] at this
    · have hnot : u ∉ P := fun hp => Finset.disjoint_left.mp (hdis.1 Q hQ) hp hu
      have := h u ⟨Q, List.mem_cons_of_mem _ hQ, hu⟩
      rwa [aux_cons, if_neg hnot] at this

def blk (n a b : ℕ) : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => a ≤ i.val ∧ i.val < b)

theorem card_prefix (n k : ℕ) (hk : k ≤ n) : (prefixJobs n k).card = k := by
  rw [← Finset.card_range k]
  apply Finset.card_bij (fun u _ => u.val)
  · intro u hu; simpa [prefixJobs] using hu
  · intro u _ v _ h; exact Fin.ext h
  · intro m hm
    have hm' : m < k := Finset.mem_range.mp hm
    exact ⟨⟨m, lt_of_lt_of_le hm' hk⟩, by simp [prefixJobs, hm'], rfl⟩

theorem blk_eq (n a b : ℕ) : blk n a b = prefixJobs n b \ prefixJobs n a := by
  ext x; simp [blk, prefixJobs]; omega

theorem card_blk (n a b : ℕ) (hab : a ≤ b) (hb : b ≤ n) : (blk n a b).card = b - a := by
  rw [blk_eq, Finset.card_sdiff_of_subset, card_prefix n b hb, card_prefix n a (hab.trans hb)]
  intro x hx; simp [prefixJobs] at hx ⊢; omega

theorem card_le_of_sub (U : Finset (Fin n)) (k : ℕ) (h : ∀ u ∈ U, u.val < k) : U.card ≤ k := by
  calc U.card ≤ (Finset.range k).card :=
        Finset.card_le_card_of_injOn (fun u => u.val) (fun u hu => by simpa using h u hu)
          (fun u _ v _ h => Fin.ext h)
    _ = k := Finset.card_range k

theorem exists_big (U : Finset (Fin n)) (c : ℕ) (hc : U.card = c) (h1 : 1 ≤ c) :
    ∃ u ∈ U, c - 1 ≤ u.val := by
  by_contra hcon
  simp only [not_exists, not_and, not_le] at hcon
  have := card_le_of_sub U (c - 1) hcon
  omega

theorem sup_blk (r : Fin n → ℕ) (hr : Monotone r) (a j0 : ℕ) (hj0 : j0 < n) (ha : a ≤ j0) :
    (blk n a (j0 + 1)).sup r = r ⟨j0, hj0⟩ := by
  apply le_antisymm
  · apply Finset.sup_le
    intro x hx
    simp only [blk, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact hr (Fin.mk_le_mk.mpr (by omega))
  · apply Finset.le_sup (f := r)
    simp [blk]; omega

end Infra

section Core
variable {n : ℕ}

theorem core (B p : ℕ) (r d : Fin n → ℕ) (hd : Monotone d) (hr : Monotone r) (j : ℕ)
    (hj : j ≤ n) :
    ∀ (S : List (Finset (Fin n))) (a t t' : ℕ) (done : Finset (Fin n)),
    (∀ P ∈ S, P.Nonempty ∧ P.card ≤ B) →
    S.Pairwise (fun P Q => Disjoint P Q) →
    (∀ P ∈ S, Disjoint P done) →
    (∀ P ∈ S, ∀ u ∈ P, u.val < j) →
    (∀ u : Fin n, u.val < j → u ∉ done → ∃ P ∈ S, u ∈ P) →
    done.card = a → (∀ u ∈ done, u.val < j) →
    t' ≤ t → done.sup r ≤ t → OT p r d S t →
    ∃ S' : List (Finset (Fin n)),
      (∀ Q ∈ S', Q.Nonempty ∧ Q.card ≤ B) ∧
      IsConsecutive S' ∧
      (∀ u : Fin n, (∃ Q ∈ S', u ∈ Q) ↔ a ≤ u.val ∧ u.val < j) ∧
      finish p r S' t' ≤ finish p r S t ∧ OT p r d S' t' := by
  intro S
  induction S with
  | nil =>
    intro a t t' done _ _ _ _ hcov hcard hdj htt _ _
    have hsub : prefixJobs n j = done := by
      apply Finset.Subset.antisymm
      · intro u hu
        have hu' : u.val < j := by simpa [prefixJobs] using hu
        by_contra hnd
        obtain ⟨P, hP, _⟩ := hcov u hu' hnd
        simp at hP
      · intro u hu; simpa [prefixJobs] using hdj u hu
    have haj : a = j := by rw [← hcard, ← hsub, card_prefix n j hj]
    refine ⟨[], by simp, ⟨by simp, by simp⟩, ?_, htt, trivial⟩
    intro u; simp; omega
  | cons P S1 ih =>
    intro a t t' done hne hdis hdd hlt hcov hcard hdj htt hsup hO
    rw [List.pairwise_cons] at hdis
    have hPne := hne P List.mem_cons_self
    set s := P.card with hs
    have hs1 : 1 ≤ s := Finset.card_pos.mpr hPne.1
    have hsB : s ≤ B := hPne.2
    have hPd : Disjoint P done := hdd P List.mem_cons_self
    have hPj : ∀ u ∈ P, u.val < j := hlt P List.mem_cons_self
    have hUcard : (done ∪ P).card = a + s := by
      rw [Finset.card_union_of_disjoint hPd.symm, hcard]
    have hUj : ∀ u ∈ done ∪ P, u.val < j := by
      intro u hu
      rcases Finset.mem_union.mp hu with h | h
      · exact hdj u h
      · exact hPj u h
    have has : a + s ≤ j := by
      have := card_le_of_sub _ j hUj
      omega
    have has_n : a + s ≤ n := has.trans hj
    -- block
    set Q := blk n a (a + s) with hQdef
    have hQcard : Q.card = s := by
      rw [hQdef, card_blk n a (a + s) (by omega) has_n]; omega
    have hQne : Q.Nonempty := Finset.card_pos.mp (by omega)
    -- release bound
    have hQsup : Q.sup r ≤ max t (P.sup r) := by
      obtain ⟨u, hu, hu2⟩ := exists_big _ _ hUcard (by omega)
      have h1 : Q.sup r ≤ r u := by
        apply Finset.sup_le
        intro x hx
        simp only [hQdef, blk, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        exact hr (Fin.le_def.mpr (by omega))
      have h2 : r u ≤ (done ∪ P).sup r := Finset.le_sup (f := r) hu
      rw [Finset.sup_union] at h2
      exact h1.trans (h2.trans (max_le_max hsup le_rfl))
    have hstp : stp p r t' Q ≤ stp p r t P :=
      Nat.add_le_add_right (max_le (htt.trans (le_max_left _ _)) hQsup) _
    -- deadlines
    have hQd : ∀ i ∈ Q, stp p r t' Q ≤ d i := by
      intro i hi
      simp only [hQdef, blk, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      have hlt' : done.card < (prefixJobs n (i.val + 1)).card := by
        rw [card_prefix n _ (by have := i.2; omega)]; omega
      obtain ⟨u, hu, hund⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt'
      have hu' : u.val < i.val + 1 := by simpa [prefixJobs] using hu
      obtain ⟨P', hP', huP'⟩ := hcov u (by omega) hund
      have hdu : stp p r t P ≤ d u := by
        rcases List.mem_cons.mp hP' with rfl | hP'
        · exact hO.1 u huP'
        · have := OT_lt p r d S1 _ u hO.2 ⟨P', hP', huP'⟩
          exact (Nat.le_add_right _ _).trans this
      have hdi : d u ≤ d i := hd (Fin.le_def.mpr (by omega))
      exact hstp.trans (hdu.trans hdi)
    -- apply IH
    have hIH := ih (a + s) (stp p r t P) (stp p r t' Q) (done ∪ P)
      (fun R hR => hne R (List.mem_cons_of_mem _ hR)) hdis.2
      (fun R hR => by
        rw [Finset.disjoint_union_right]
        exact ⟨hdd R (List.mem_cons_of_mem _ hR), (hdis.1 R hR).symm⟩)
      (fun R hR => hlt R (List.mem_cons_of_mem _ hR))
      (fun u hu hnd => by
        have hnd' : u ∉ done := fun h => hnd (Finset.mem_union_left _ h)
        have hnP : u ∉ P := fun h => hnd (Finset.mem_union_right _ h)
        obtain ⟨R, hR, huR⟩ := hcov u hu hnd'
        rcases List.mem_cons.mp hR with rfl | hR
        · exact absurd huR hnP
        · exact ⟨R, hR, huR⟩)
      hUcard hUj hstp
      (by
        rw [Finset.sup_union]
        exact max_le ((hsup.trans (le_max_left _ _)).trans (Nat.le_add_right _ _))
          ((le_max_right _ _).trans (Nat.le_add_right _ _)))
      hO.2
    obtain ⟨S'', hne'', hcons'', hcov'', hfin'', hOT''⟩ := hIH
    refine ⟨Q :: S'', ?_, ?_, ?_, ?_, ?_⟩
    · intro R hR
      rcases List.mem_cons.mp hR with rfl | hR
      · exact ⟨hQne, by omega⟩
      · exact hne'' R hR
    · refine ⟨?_, ?_⟩
      · intro R hR
        rcases List.mem_cons.mp hR with rfl | hR
        · exact ⟨a, a + s, rfl⟩
        · exact hcons''.1 R hR
      · rw [List.pairwise_cons]
        refine ⟨?_, hcons''.2⟩
        intro R hR i hi k hk
        have hk' := (hcov'' k).mp ⟨R, hR, hk⟩
        simp only [hQdef, blk, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        exact Fin.lt_def.mpr (by omega)
    · intro u
      constructor
      · rintro ⟨R, hR, huR⟩
        rcases List.mem_cons.mp hR with rfl | hR
        · simp only [hQdef, blk, Finset.mem_filter, Finset.mem_univ, true_and] at huR
          omega
        · have := (hcov'' u).mp ⟨R, hR, huR⟩; omega
      · intro hu
        by_cases h : u.val < a + s
        · exact ⟨Q, List.mem_cons_self, by simp [hQdef, blk]; omega⟩
        · obtain ⟨R, hR, huR⟩ := (hcov'' u).mpr ⟨by omega, hu.2⟩
          exact ⟨R, List.mem_cons_of_mem _ hR, huR⟩
    · rw [finish_cons, finish_cons]; exact hfin''
    · exact ⟨hQd, hOT''⟩

end Core

theorem allOnTime_OT {n : ℕ} (p : ℕ) (r d : Fin n → ℕ) (J : Finset (Fin n))
    (S : List (Finset (Fin n))) (hdis : S.Pairwise (fun P Q => Disjoint P Q))
    (hcov : ∀ u : Fin n, (∃ P ∈ S, u ∈ P) → u ∈ J) (h : AllOnTime p r d J S) :
    OT p r d S 0 :=
  OT_of_aux p r d S 0 hdis (fun u hu => h u (hcov u hu))

theorem OT_allOnTime {n : ℕ} (p : ℕ) (r d : Fin n → ℕ) (J : Finset (Fin n))
    (S : List (Finset (Fin n))) (hcov : ∀ u : Fin n, u ∈ J → ∃ P ∈ S, u ∈ P)
    (h : OT p r d S 0) : AllOnTime p r d J S :=
  fun u hu => aux_le p r d S 0 u h (hcov u hu)

theorem consecutive_batches_core {n : ℕ} (B p : ℕ) (r d : Fin n → ℕ)
    (hd : Monotone d) (hr : Monotone r) (j : ℕ) (hj : j ≤ n)
    (S : List (Finset (Fin n))) (hS : IsBatchSchedule B (prefixJobs n j) S)
    (hon : AllOnTime p r d (prefixJobs n j) S) :
    ∃ S' : List (Finset (Fin n)),
      IsBatchSchedule B (prefixJobs n j) S' ∧ AllOnTime p r d (prefixJobs n j) S' ∧
      IsConsecutive S' ∧ makespan p r S' ≤ makespan p r S := by
  obtain ⟨h1, h2, h3⟩ := hS
  have hmem : ∀ u : Fin n, (∃ P ∈ S, u ∈ P) ↔ u ∈ prefixJobs n j := fun u => (h3 u).symm
  have hOT : OT p r d S 0 :=
    allOnTime_OT p r d _ S h2 (fun u hu => (hmem u).mp hu) hon
  obtain ⟨S', hne, hcons, hcov, hfin, hOT'⟩ := core B p r d hd hr j hj S 0 0 0 ∅ h1 h2
    (fun P _ => Finset.disjoint_empty_right P)
    (fun P hP u hu => by have := (hmem u).mp ⟨P, hP, hu⟩; simpa [prefixJobs] using this)
    (fun u hu _ => (hmem u).mpr (by simpa [prefixJobs] using hu))
    (by simp) (by simp) le_rfl (by simp) hOT
  have hcov' : ∀ u : Fin n, (∃ Q ∈ S', u ∈ Q) ↔ u ∈ prefixJobs n j := by
    intro u; rw [hcov u]; simp [prefixJobs]
  refine ⟨S', ⟨hne, ?_, fun u => (hcov' u).symm⟩, ?_, hcons, hfin⟩
  · refine hcons.2.imp ?_
    intro P Q h
    rw [Finset.disjoint_left]
    intro x hxP hxQ
    exact lt_irrefl _ (h x hxP x hxQ)
  · exact OT_allOnTime p r d _ S' (fun u hu => (hcov' u).mpr hu) hOT'

theorem prefix_n (n : ℕ) : prefixJobs n n = Finset.univ := by
  ext x; simp [prefixJobs]

section Transport
variable {n : ℕ}

def tr (e : Fin n ≃ Fin n) (S : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  S.map (fun P => P.image e)

theorem stp_image (p : ℕ) (r' : Fin n → ℕ) (e : Fin n ≃ Fin n) (t : ℕ) (P : Finset (Fin n)) :
    stp p r' t (P.image e) = stp p (r' ∘ e) t P := by
  simp [stp, Finset.sup_image]

theorem finish_tr (p : ℕ) (r' : Fin n → ℕ) (e : Fin n ≃ Fin n) (S : List (Finset (Fin n))) :
    ∀ t, finish p r' (tr e S) t = finish p (r' ∘ e) S t := by
  induction S with
  | nil => intro t; rfl
  | cons P S ih =>
    intro t
    show finish p r' ((P.image e) :: tr e S) t = _
    rw [finish_cons, stp_image, ih, finish_cons]

theorem aux_tr (p : ℕ) (r' : Fin n → ℕ) (e : Fin n ≃ Fin n) (S : List (Finset (Fin n))) (u : Fin n) :
    ∀ t, jobCompletionAux p r' (e u) (tr e S) t = jobCompletionAux p (r' ∘ e) u S t := by
  induction S with
  | nil => intro t; rfl
  | cons P S ih =>
    intro t
    show jobCompletionAux p r' (e u) ((P.image e) :: tr e S) t = _
    rw [aux_cons, aux_cons, stp_image, ih]
    have hmem : e u ∈ P.image e ↔ u ∈ P := by simp
    simp only [hmem]

theorem tr_ok (B p : ℕ) (r' d' : Fin n → ℕ) (e : Fin n ≃ Fin n) (J : Finset (Fin n))
    (S : List (Finset (Fin n))) (hS : IsBatchSchedule B J S)
    (hon : AllOnTime p (r' ∘ e) (d' ∘ e) J S) :
    IsBatchSchedule B (J.image e) (tr e S) ∧ AllOnTime p r' d' (J.image e) (tr e S) ∧
      makespan p r' (tr e S) = makespan p (r' ∘ e) S := by
  obtain ⟨h1, h2, h3⟩ := hS
  refine ⟨⟨?_, ?_, ?_⟩, ?_, finish_tr p r' e S 0⟩
  · intro Q hQ
    obtain ⟨P, hP, rfl⟩ := List.mem_map.mp hQ
    exact ⟨((h1 P hP).1).image e, by rw [Finset.card_image_of_injective _ e.injective]; exact (h1 P hP).2⟩
  · exact List.pairwise_map.mpr (h2.imp fun {P Q} h => (Finset.disjoint_image e.injective).mpr h)
  · intro j
    constructor
    · intro hj
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hj
      obtain ⟨P, hP, hxP⟩ := (h3 x).mp hx
      exact ⟨P.image e, List.mem_map.mpr ⟨P, hP, rfl⟩, Finset.mem_image_of_mem e hxP⟩
    · rintro ⟨Q, hQ, hjQ⟩
      obtain ⟨P, hP, rfl⟩ := List.mem_map.mp hQ
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hjQ
      exact Finset.mem_image_of_mem e ((h3 x).mpr ⟨P, hP, hx⟩)
  · intro u hu
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
    have := hon x hx
    unfold jobCompletion at this ⊢
    rw [aux_tr]
    exact this

end Transport

theorem lemma_1_core {n : ℕ} (B p : ℕ) (r d : Fin n → ℕ)
    (hagree : ∀ i j : Fin n, r i < r j → d i ≤ d j)
    (hfeas : ∃ S : List (Finset (Fin n)),
      IsBatchSchedule B Finset.univ S ∧ AllOnTime p r d Finset.univ S) :
    ∃ S : List (Finset (Fin n)),
      IsBatchSchedule B Finset.univ S ∧ AllOnTime p r d Finset.univ S ∧ IsBatchEDD d S := by
  obtain ⟨S, hS, hon⟩ := hfeas
  set σ : Equiv.Perm (Fin n) := Tuple.sort (fun i => toLex (d i, r i)) with hσ
  have hmono : Monotone ((fun i => toLex (d i, r i)) ∘ σ) :=
    Tuple.monotone_sort (fun i => toLex (d i, r i))
  have hdm : Monotone (d ∘ σ) := by
    intro x y hxy
    have := hmono hxy
    simp only [Function.comp, Prod.Lex.le_iff] at this
    simp only [Function.comp]
    rcases this with h | h
    · exact h.le
    · exact h.1.le
  have hrm : Monotone (r ∘ σ) := by
    intro x y hxy
    have := hmono hxy
    simp only [Function.comp, Prod.Lex.le_iff] at this
    simp only [Function.comp]
    rcases this with h | h
    · by_contra hc
      exact absurd (hagree _ _ (not_le.mp hc)) (not_le.mpr h)
    · exact h.2
  have e1 : (r ∘ σ) ∘ σ.symm = r := by funext x; simp
  have e2 : (d ∘ σ) ∘ σ.symm = d := by funext x; simp
  obtain ⟨hS1, hon1, -⟩ := tr_ok B p (r ∘ σ) (d ∘ σ) σ.symm Finset.univ S hS
    (by rw [e1, e2]; exact hon)
  rw [Finset.image_univ_equiv] at hS1
  rw [Finset.image_univ_equiv] at hon1
  rw [← prefix_n n] at hS1 hon1
  obtain ⟨S', hS', hon', hcons, -⟩ :=
    consecutive_batches_core B p (r ∘ σ) (d ∘ σ) hdm hrm n le_rfl _ hS1 hon1
  rw [prefix_n] at hS' hon'
  obtain ⟨hS2, hon2, -⟩ := tr_ok B p r d σ Finset.univ S' hS' hon'
  rw [Finset.image_univ_equiv] at hS2 hon2
  refine ⟨tr σ S', hS2, hon2, ?_⟩
  unfold tr
  rw [IsBatchEDD, List.pairwise_map]
  refine hcons.2.imp ?_
  intro P Q h i hi k hk
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hi
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hk
  exact hdm (h x hx y hy).le

theorem sing_aux {n : ℕ} (p : ℕ) (r : Fin n → ℕ) : ∀ (L : List (Fin n)),
    L.Pairwise (fun a b => r a ≤ r b) → ∀ (t : ℕ) (u : Fin n), u ∈ L →
    ∃ k, k < L.length ∧
      jobCompletionAux p r u (L.map (fun a => ({a} : Finset (Fin n)))) t ≤
        max t (r u) + (k + 1) * p := by
  intro L
  induction L with
  | nil => intro _ t u hu; simp at hu
  | cons a L ih =>
    intro hL t u hu
    rw [List.pairwise_cons] at hL
    show ∃ k, k < (a :: L).length ∧
      jobCompletionAux p r u (({a} : Finset (Fin n)) :: L.map (fun a => ({a} : Finset (Fin n)))) t ≤ _
    rw [aux_cons]
    by_cases hua : u ∈ ({a} : Finset (Fin n))
    · rw [if_pos hua]
      have : u = a := by simpa using hua
      subst this
      refine ⟨0, by simp, ?_⟩
      simp [stp]
    · rw [if_neg hua]
      have huL : u ∈ L := by
        rcases List.mem_cons.mp hu with h | h
        · exact absurd (by simp [h]) hua
        · exact h
      obtain ⟨k, hk, hle⟩ := ih hL.2 (stp p r t {a}) u huL
      refine ⟨k + 1, by simp; omega, ?_⟩
      have hra : r a ≤ r u := hL.1 u huL
      have hs : stp p r t {a} = max t (r a) + p := by simp [stp]
      rw [hs] at hle
      have h1 : (k + 1 + 1) * p = (k + 1) * p + p := by ring
      rw [h1]
      rw [hs]
      refine hle.trans ?_
      have : max (max t (r a) + p) (r u) ≤ max t (r u) + p := by omega
      omega

theorem lemma_2_core {n : ℕ} (B p : ℕ) (r d : Fin n → ℕ) (hB : 0 < B)
    (hrd : ∀ j : Fin n, r j + p ≤ d j) :
    ∃ S : List (Finset (Fin n)),
      IsBatchSchedule B Finset.univ S ∧ tmax p r d Finset.univ S ≤ (n - 1) * p := by
  set σ : Equiv.Perm (Fin n) := Tuple.sort r with hσ
  have hmono : Monotone (r ∘ σ) := Tuple.monotone_sort r
  set L : List (Fin n) := List.ofFn σ with hL
  have hLlen : L.length = n := by simp [hL]
  have hLmem : ∀ u : Fin n, u ∈ L := by
    intro u; rw [hL, List.mem_ofFn]; exact ⟨σ.symm u, by simp⟩
  have hLnd : L.Nodup := List.nodup_ofFn.mpr σ.injective
  have hLsort : L.Pairwise (fun a b => r a ≤ r b) := by
    rw [hL, List.pairwise_ofFn]
    intro i k hik
    exact hmono hik.le
  refine ⟨L.map (fun a => ({a} : Finset (Fin n))), ⟨?_, ?_, ?_⟩, ?_⟩
  · intro P hP
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hP
    exact ⟨Finset.singleton_nonempty a, by simpa using Nat.succ_le_of_lt hB⟩
  · exact List.pairwise_map.mpr (hLnd.imp fun {a b} h => Finset.disjoint_singleton.mpr h)
  · intro j
    refine ⟨fun _ => ⟨{j}, List.mem_map.mpr ⟨j, hLmem j, rfl⟩, by simp⟩, fun _ => Finset.mem_univ _⟩
  · unfold tmax
    apply Finset.sup_le
    intro u _
    obtain ⟨k, hk, hle⟩ := sing_aux p r L hLsort 0 u (hLmem u)
    unfold jobCompletion
    have h1 : (k + 1) * p = k * p + p := by ring
    have h2 : k * p ≤ (n - 1) * p := Nat.mul_le_mul_right _ (by omega)
    have h3 := hrd u
    simp only [zero_le, max_eq_right] at hle
    omega

end BurnInBatch.ReleaseTmax

open BurnInBatch.ReleaseTmax


theorem solution {n : ℕ} (B p : ℕ) (r d : Fin n → ℕ)
    (hagree : ∀ i j : Fin n, r i < r j → d i ≤ d j)
    (hfeas : ∃ S : List (Finset (Fin n)),
      IsBatchSchedule B Finset.univ S ∧ AllOnTime p r d Finset.univ S) :
    ∃ S : List (Finset (Fin n)),
      IsBatchSchedule B Finset.univ S ∧ AllOnTime p r d Finset.univ S ∧ IsBatchEDD d S := by
  exact lemma_1_core B p r d hagree hfeas
