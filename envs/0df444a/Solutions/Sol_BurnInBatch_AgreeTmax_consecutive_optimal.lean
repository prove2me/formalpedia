-- Prove2me | solution 1 for BurnInBatch.AgreeTmax.consecutive_optimal
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T02:30:59.751069+00:00
-- url     : https://prove2.me/submissions/ec5d08a7-fdab-4ecc-93e0-644034ff2019

import Mathlib
import Definitions.Def_BurnInBatch_AgreeTmax_Model



namespace BurnInBatch.AgreeTmax
namespace Core

set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

variable {α : Type*} [DecidableEq α]

def tm (p : α → ℕ) (P : Finset α) : ℕ := P.sup p

def tms (p : α → ℕ) (S : List (Finset α)) : ℕ := (S.map (tm p)).sum

def Feas (p d : α → ℕ) : ℕ → List (Finset α) → Prop
  | _, [] => True
  | θ, P :: R => (∀ i ∈ P, θ + tm p P ≤ d i) ∧ Feas p d (θ + tm p P) R

def Valid (cap : ℕ) (J : Finset α) (S : List (Finset α)) : Prop :=
  (∀ P ∈ S, P.Nonempty) ∧ (∀ P ∈ S, P.card ≤ cap) ∧ (∀ P ∈ S, P ⊆ J) ∧
    S.Pairwise Disjoint ∧ ∀ i ∈ J, ∃ P ∈ S, i ∈ P

noncomputable def mn (r : α → ℕ) (P : Finset α) : ℕ := sInf (r '' (P : Set α))

theorem mn_le {r : α → ℕ} {P : Finset α} {x : α} (hx : x ∈ P) : mn r P ≤ r x :=
  Nat.sInf_le ⟨x, hx, rfl⟩

theorem exists_mn {r : α → ℕ} {P : Finset α} (h : P.Nonempty) : ∃ x ∈ P, r x = mn r P := by
  have : (r '' (P : Set α)).Nonempty := Set.Nonempty.image r (Finset.coe_nonempty.mpr h)
  obtain ⟨x, hx, hxe⟩ := Nat.sInf_mem this
  exact ⟨x, hx, hxe⟩

theorem le_mn {r : α → ℕ} {P : Finset α} {c : ℕ} (h : P.Nonempty) (hx : ∀ x ∈ P, c ≤ r x) :
    c ≤ mn r P := by
  obtain ⟨x, hxP, e⟩ := exists_mn (r := r) h
  rw [← e]; exact hx x hxP

theorem lt_mn {r : α → ℕ} {P : Finset α} {c : ℕ} (h : P.Nonempty) (hx : ∀ x ∈ P, c < r x) :
    c < mn r P := by
  obtain ⟨x, hxP, e⟩ := exists_mn (r := r) h
  rw [← e]; exact hx x hxP

theorem tm_le {p : α → ℕ} {P : Finset α} {x : α} (hx : x ∈ P) : p x ≤ tm p P :=
  Finset.le_sup (f := p) hx

theorem tm_le_of {p : α → ℕ} {P : Finset α} {c : ℕ} (h : ∀ x ∈ P, p x ≤ c) : tm p P ≤ c :=
  Finset.sup_le h

theorem tm_union (p : α → ℕ) (A B : Finset α) : tm p (A ∪ B) = max (tm p A) (tm p B) :=
  Finset.sup_union

theorem feas_mono {p d : α → ℕ} : ∀ (S : List (Finset α)) {θ θ' : ℕ}, θ' ≤ θ →
    Feas p d θ S → Feas p d θ' S := by
  intro S
  induction S with
  | nil => intros; trivial
  | cons P R ih =>
    intro θ θ' h hf
    refine ⟨fun i hi => le_trans (by omega) (hf.1 i hi), ih (by omega) hf.2⟩

theorem tms_append (p : α → ℕ) (S1 S2 : List (Finset α)) :
    tms p (S1 ++ S2) = tms p S1 + tms p S2 := by
  simp [tms]

theorem feas_append {p d : α → ℕ} : ∀ (S1 S2 : List (Finset α)) (θ : ℕ),
    Feas p d θ (S1 ++ S2) ↔ Feas p d θ S1 ∧ Feas p d (θ + tms p S1) S2 := by
  intro S1
  induction S1 with
  | nil => intro S2 θ; simp [Feas, tms]
  | cons P R ih =>
    intro S2 θ
    have e : θ + tms p (P :: R) = θ + tm p P + tms p R := by simp [tms]; omega
    simp only [List.cons_append, Feas, ih, e]
    tauto

theorem feas_insert {p d r : α → ℕ} (hd : ∀ x y, r x ≤ r y → d x ≤ d y) :
    ∀ (s : List (Finset α)) (a : Finset α), (∀ P ∈ s, P.Nonempty) →
      ∀ θ, Feas p d θ (a :: s) →
        Feas p d θ (List.orderedInsert (fun A B => mn r A ≤ mn r B) a s) := by
  intro s
  induction s with
  | nil => intro a _ θ h; simpa [Feas] using h
  | cons b s' ih =>
    intro a hne θ h
    rw [List.orderedInsert_cons]
    by_cases hab : mn r a ≤ mn r b
    · rw [if_pos hab]; exact h
    · rw [if_neg hab]
      have hbne : b.Nonempty := hne b List.mem_cons_self
      obtain ⟨μ, hμ, hμe⟩ := exists_mn (r := r) hbne
      obtain ⟨ha1, hb1, hs⟩ : (∀ i ∈ a, θ + tm p a ≤ d i) ∧ (∀ i ∈ b, θ + tm p a + tm p b ≤ d i) ∧
          Feas p d (θ + tm p a + tm p b) s' := ⟨h.1, h.2.1, h.2.2⟩
      refine ⟨fun i hi => le_trans (by omega) (hb1 i hi), ?_⟩
      apply ih a (fun P hP => hne P (List.mem_cons_of_mem _ hP))
      refine ⟨fun i hi => ?_, ?_⟩
      · have h1 : r μ ≤ r i := by
          have := mn_le (r := r) hi
          omega
        have h2 := hd μ i h1
        have h3 := hb1 μ hμ
        omega
      · have : θ + tm p b + tm p a = θ + tm p a + tm p b := by omega
        rw [this]; exact hs

theorem feas_sort {p d r : α → ℕ} (hd : ∀ x y, r x ≤ r y → d x ≤ d y) :
    ∀ (S : List (Finset α)), (∀ P ∈ S, P.Nonempty) → ∀ θ, Feas p d θ S →
      Feas p d θ (List.insertionSort (fun A B => mn r A ≤ mn r B) S) := by
  intro S
  induction S with
  | nil => intro _ θ h; simpa [Feas] using h
  | cons a l ih =>
    intro hne θ h
    rw [List.insertionSort_cons]
    apply feas_insert hd _ a
    · intro P hP
      exact hne P (List.mem_cons_of_mem _ ((List.perm_insertionSort _ l).subset hP))
    · refine ⟨h.1, ?_⟩
      exact ih (fun P hP => hne P (List.mem_cons_of_mem _ hP)) _ h.2


theorem exchange {r p d : α → ℕ} (hinj : Function.Injective r)
    (hp : ∀ x y, r x ≤ r y → p x ≤ p y) (hd : ∀ x y, r x ≤ r y → d x ≤ d y)
    {cap θ : ℕ} {A B : Finset α} (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hAc : A.card ≤ cap) (hBc : B.card ≤ cap) (hdisj : Disjoint A B)
    (hA : ∀ i ∈ A, θ + tm p A ≤ d i) (hB : ∀ i ∈ B, θ + tm p A + tm p B ≤ d i)
    (hlt : mn r A < mn r B) (hcross : ∃ u ∈ A, mn r B < r u) :
    ∃ A' B' : Finset α, A'.Nonempty ∧ B'.Nonempty ∧ A'.card ≤ cap ∧ B'.card ≤ cap ∧
      Disjoint A' B' ∧ A' ∪ B' = A ∪ B ∧ tm p A' + tm p B' ≤ tm p A + tm p B ∧
      (∀ i ∈ A', θ + tm p A' ≤ d i) ∧ (∀ i ∈ B', θ + tm p A' + tm p B' ≤ d i) ∧
      mn r A + mn r B < mn r A' + mn r B' := by
  obtain ⟨v0, hv0B, hv0e⟩ := exists_mn (r := r) hBne
  obtain ⟨a0, ha0A, ha0e⟩ := exists_mn (r := r) hAne
  have hBge : ∀ y ∈ B, r v0 ≤ r y := fun y hy => by rw [hv0e]; exact mn_le hy
  have hBgt : ∀ y ∈ B, y ≠ v0 → r v0 < r y := fun y hy hne =>
    lt_of_le_of_ne (hBge y hy) (fun h => hne (hinj h).symm)
  have hnotA : ∀ x ∈ B, x ∉ A := fun x hx hxA => Finset.disjoint_left.mp hdisj hxA hx
  have hv0A : v0 ∉ A := hnotA v0 hv0B
  have hAB : ∀ x ∈ A, x ∉ B := fun x hx hxB => Finset.disjoint_left.mp hdisj hx hxB
  have hr0 : r a0 < r v0 := by rw [ha0e, hv0e]; exact hlt
  have hv0B' : θ + tm p A + tm p B ≤ d v0 := hB v0 hv0B
  by_cases hc1 : ∃ u ∈ A, r v0 < r u ∧ p u ≤ tm p B
  · obtain ⟨u, huA, hu1, hu2⟩ := hc1
    have huB : u ∉ B := hAB u huA
    have hua0 : u ≠ a0 := fun h => by subst h; omega
    have huv0 : u ≠ v0 := fun h => hv0A (h ▸ huA)
    have hv0' : v0 ∉ A.erase u := fun h => hv0A (Finset.mem_of_mem_erase h)
    have hu' : u ∉ B.erase v0 := fun h => huB (Finset.mem_of_mem_erase h)
    refine ⟨insert v0 (A.erase u), insert u (B.erase v0), Finset.insert_nonempty _ _,
      Finset.insert_nonempty _ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hv0', Finset.card_erase_of_mem huA]
      have := Finset.card_pos.mpr hAne; omega
    · rw [Finset.card_insert_of_notMem hu', Finset.card_erase_of_mem hv0B]
      have := Finset.card_pos.mpr hBne; omega
    · rw [Finset.disjoint_left]
      intro x hx hx'
      rw [Finset.mem_insert, Finset.mem_erase] at hx hx'
      rcases hx with rfl | ⟨hx1, hx2⟩
      · rcases hx' with h | ⟨h1, _⟩
        · exact huv0 h.symm
        · exact h1 rfl
      · rcases hx' with rfl | ⟨_, h2⟩
        · exact hx1 rfl
        · exact hAB x hx2 h2
    · ext x
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
      by_cases hxu : x = u
      · subst hxu; simp [huA]
      · by_cases hxv : x = v0
        · subst hxv; simp [hv0B]
        · simp [hxu, hxv]
    · apply le_trans (add_le_add (b := tm p A) (d := tm p B) ?_ ?_) le_rfl
      · apply tm_le_of
        intro x hx
        rw [Finset.mem_insert, Finset.mem_erase] at hx
        rcases hx with rfl | ⟨_, hx2⟩
        · exact le_trans (hp _ _ hu1.le) (tm_le huA)
        · exact tm_le hx2
      · apply tm_le_of
        intro x hx
        rw [Finset.mem_insert, Finset.mem_erase] at hx
        rcases hx with rfl | ⟨_, hx2⟩
        · exact hu2
        · exact tm_le hx2
    · intro i hi
      have hA'le : tm p (insert v0 (A.erase u)) ≤ tm p A := by
        apply tm_le_of
        intro x hx
        rw [Finset.mem_insert, Finset.mem_erase] at hx
        rcases hx with rfl | ⟨_, hx2⟩
        · exact le_trans (hp _ _ hu1.le) (tm_le huA)
        · exact tm_le hx2
      rw [Finset.mem_insert, Finset.mem_erase] at hi
      rcases hi with rfl | ⟨_, hi2⟩
      · have := hA a0 ha0A
        have := hd a0 i hr0.le
        omega
      · have := hA i hi2; omega
    · intro i hi
      have hA'le : tm p (insert v0 (A.erase u)) ≤ tm p A := by
        apply tm_le_of
        intro x hx
        rw [Finset.mem_insert, Finset.mem_erase] at hx
        rcases hx with rfl | ⟨_, hx2⟩
        · exact le_trans (hp _ _ hu1.le) (tm_le huA)
        · exact tm_le hx2
      have hB'le : tm p (insert u (B.erase v0)) ≤ tm p B := by
        apply tm_le_of
        intro x hx
        rw [Finset.mem_insert, Finset.mem_erase] at hx
        rcases hx with rfl | ⟨_, hx2⟩
        · exact hu2
        · exact tm_le hx2
      rw [Finset.mem_insert, Finset.mem_erase] at hi
      rcases hi with rfl | ⟨_, hi2⟩
      · have := hd v0 i hu1.le
        omega
      · have := hB i hi2; omega
    · have h1 : mn r A ≤ mn r (insert v0 (A.erase u)) := by
        apply le_mn (Finset.insert_nonempty _ _)
        intro x hx
        rw [Finset.mem_insert, Finset.mem_erase] at hx
        rcases hx with rfl | ⟨_, hx2⟩
        · omega
        · exact mn_le hx2
      have h2 : mn r B < mn r (insert u (B.erase v0)) := by
        apply lt_mn (Finset.insert_nonempty _ _)
        intro x hx
        rw [Finset.mem_insert, Finset.mem_erase] at hx
        rcases hx with rfl | ⟨hx1, hx2⟩
        · omega
        · have := hBgt x hx2 hx1; omega
      omega
  · push_neg at hc1
    obtain ⟨u1, hu1A, hu1⟩ := hcross
    have hu1' : r v0 < r u1 := by rw [hv0e]; exact hu1
    set H := A.filter (fun u => r v0 < r u) with hH
    set L := A.filter (fun u => ¬ r v0 < r u) with hL
    have hHne : H.Nonempty := ⟨u1, Finset.mem_filter.mpr ⟨hu1A, hu1'⟩⟩
    have ha0L : a0 ∈ L := Finset.mem_filter.mpr ⟨ha0A, by omega⟩
    have hHA : H ⊆ A := Finset.filter_subset _ _
    have hLA : L ⊆ A := Finset.filter_subset _ _
    have hHL : Disjoint L H := by
      rw [Finset.disjoint_left]
      intro x hxL hxH
      exact (Finset.mem_filter.mp hxL).2 (Finset.mem_filter.mp hxH).2
    have hLH : L ∪ H = A := by
      rw [Finset.union_comm]; exact Finset.filter_union_filter_not_eq _ _
    have hcardLH : L.card + H.card = A.card := by
      rw [← Finset.card_union_of_disjoint hHL, hLH]
    have hHcard : 1 ≤ H.card := Finset.card_pos.mpr hHne
    have hBcard : 1 ≤ B.card := Finset.card_pos.mpr hBne
    obtain ⟨X, hvX, hXB, hXcard⟩ := Finset.exists_subsuperset_card_eq
      (s := {v0}) (t := B) (n := min H.card B.card) (by simpa using hv0B)
      (by rw [Finset.card_singleton]; exact le_min hHcard hBcard) (min_le_right _ _)
    have hv0X : v0 ∈ X := hvX (Finset.mem_singleton_self _)
    have hLtmB : tm p L ≤ tm p B := by
      apply tm_le_of
      intro x hx
      have := (Finset.mem_filter.mp hx).2
      have h1 : r x ≤ r v0 := by omega
      exact le_trans (hp _ _ h1) (tm_le hv0B)
    obtain ⟨h1, h1A, h1r⟩ : ∃ h ∈ H, True := ⟨u1, Finset.mem_filter.mpr ⟨hu1A, hu1'⟩, trivial⟩
    have hBA : tm p B < tm p A := by
      have h1m := Finset.mem_filter.mp h1A
      exact lt_of_lt_of_le (hc1 h1 h1m.1 h1m.2) (tm_le h1m.1)
    have hXtm : tm p X ≤ tm p B := Finset.sup_mono hXB
    have hSDtm : tm p (B \ X) ≤ tm p B := Finset.sup_mono Finset.sdiff_subset
    have hHtm : tm p H ≤ tm p A := Finset.sup_mono hHA
    have hA'tm : tm p (L ∪ X) ≤ tm p B := by
      rw [tm_union]; exact max_le hLtmB hXtm
    have hB'tm : tm p ((B \ X) ∪ H) ≤ tm p A := by
      rw [tm_union]; exact max_le (by omega) hHtm
    have hXdis : Disjoint L X := by
      rw [Finset.disjoint_left]; intro x hx hxX
      exact hAB x (hLA hx) (hXB hxX)
    have hSDH : Disjoint (B \ X) H := by
      rw [Finset.disjoint_left]; intro x hx hxH
      exact hAB x (hHA hxH) (Finset.mem_sdiff.mp hx).1
    refine ⟨L ∪ X, (B \ X) ∪ H, ⟨a0, Finset.mem_union_left _ ha0L⟩,
      hHne.mono (Finset.subset_union_right), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Finset.card_union_of_disjoint hXdis]
      have : X.card ≤ H.card := by rw [hXcard]; exact min_le_left _ _
      omega
    · rw [Finset.card_union_of_disjoint hSDH, Finset.card_sdiff_of_subset hXB]
      rcases le_total H.card B.card with h | h
      · rw [min_eq_left h] at hXcard; omega
      · rw [min_eq_right h] at hXcard; omega
    · rw [Finset.disjoint_union_left, Finset.disjoint_union_right, Finset.disjoint_union_right]
      refine ⟨⟨?_, hHL⟩, ⟨?_, ?_⟩⟩
      · rw [Finset.disjoint_left]; intro x hx hxs
        exact hAB x (hLA hx) (Finset.mem_sdiff.mp hxs).1
      · exact Finset.disjoint_sdiff
      · rw [Finset.disjoint_left]; intro x hx hxH
        exact hAB x (hHA hxH) (hXB hx)
    · have hBeq : X ∪ (B \ X) = B := Finset.union_sdiff_of_subset hXB
      calc L ∪ X ∪ (B \ X ∪ H) = (L ∪ H) ∪ (X ∪ (B \ X)) := by
            ext x; simp only [Finset.mem_union]; tauto
        _ = A ∪ B := by rw [hLH, hBeq]
    · omega
    · intro i hi
      rcases Finset.mem_union.mp hi with h | h
      · have := hA i (hLA h); omega
      · have := hB i (hXB h); omega
    · intro i hi
      rcases Finset.mem_union.mp hi with h | h
      · have := hB i (Finset.mem_sdiff.mp h).1; omega
      · have hh := Finset.mem_filter.mp h
        have := hd v0 i hh.2.le
        omega
    · have h1 : mn r A ≤ mn r (L ∪ X) := by
        apply le_mn ⟨a0, Finset.mem_union_left _ ha0L⟩
        intro x hx
        rcases Finset.mem_union.mp hx with h | h
        · exact mn_le (hLA h)
        · have := mn_le (r := r) (hXB h); omega
      have h2 : mn r B < mn r ((B \ X) ∪ H) := by
        apply lt_mn (hHne.mono Finset.subset_union_right)
        intro x hx
        rcases Finset.mem_union.mp hx with h | h
        · have hh := Finset.mem_sdiff.mp h
          have hne : x ≠ v0 := fun e => hh.2 (e ▸ hv0X)
          have := hBgt x hh.1 hne; omega
        · have hh := Finset.mem_filter.mp h
          omega
      omega

theorem valid_perm {cap : ℕ} {J : Finset α} {S S' : List (Finset α)} (h : S.Perm S')
    (hv : Valid cap J S) : Valid cap J S' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hv
  refine ⟨fun P hP => h1 P (h.symm.subset hP), fun P hP => h2 P (h.symm.subset hP),
    fun P hP => h3 P (h.symm.subset hP), h.pairwise h4 (fun hd => hd.symm), fun i hi => ?_⟩
  obtain ⟨P, hP, hiP⟩ := h5 i hi
  exact ⟨P, h.subset hP, hiP⟩

theorem valid_replace {cap : ℕ} {J : Finset α} {pre post : List (Finset α)} {A B A' B' : Finset α}
    (hv : Valid cap J (pre ++ A :: B :: post))
    (hA'ne : A'.Nonempty) (hB'ne : B'.Nonempty) (hA'c : A'.card ≤ cap) (hB'c : B'.card ≤ cap)
    (hdis : Disjoint A' B') (hun : A' ∪ B' = A ∪ B) :
    Valid cap J (pre ++ A' :: B' :: post) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hv
  have hAB : A ∪ B ⊆ J := Finset.union_subset (h3 A (by simp)) (h3 B (by simp))
  have hA'J : A' ⊆ J := (Finset.subset_union_left (s₂ := B')).trans (hun ▸ hAB)
  have hB'J : B' ⊆ J := (Finset.subset_union_right (s₁ := A')).trans (hun ▸ hAB)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro P hP
    simp only [List.mem_append, List.mem_cons] at hP
    rcases hP with hP | rfl | rfl | hP
    · exact h1 P (by simp [hP])
    · exact hA'ne
    · exact hB'ne
    · exact h1 P (by simp [hP])
  · intro P hP
    simp only [List.mem_append, List.mem_cons] at hP
    rcases hP with hP | rfl | rfl | hP
    · exact h2 P (by simp [hP])
    · exact hA'c
    · exact hB'c
    · exact h2 P (by simp [hP])
  · intro P hP
    simp only [List.mem_append, List.mem_cons] at hP
    rcases hP with hP | rfl | rfl | hP
    · exact h3 P (by simp [hP])
    · exact hA'J
    · exact hB'J
    · exact h3 P (by simp [hP])
  · simp only [List.pairwise_append, List.pairwise_cons, List.mem_cons] at h4 ⊢
    obtain ⟨hpre, ⟨hApost, hBpost, hpost⟩, hcross⟩ := h4
    have hU : ∀ x, Disjoint x A → Disjoint x B → Disjoint x A' ∧ Disjoint x B' := by
      intro x hxA hxB
      have h : Disjoint x (A' ∪ B') := by rw [hun]; exact Finset.disjoint_union_right.mpr ⟨hxA, hxB⟩
      exact ⟨Finset.disjoint_of_subset_right Finset.subset_union_left h,
        Finset.disjoint_of_subset_right Finset.subset_union_right h⟩
    have hAp : ∀ b ∈ post, Disjoint A b := fun b hb => hApost b (Or.inr hb)
    refine ⟨hpre, ⟨?_, ?_, hpost⟩, ?_⟩
    · intro b hb
      rcases hb with rfl | hb
      · exact hdis
      · exact (hU b (hAp b hb).symm (hBpost b hb).symm).1.symm
    · intro b hb
      exact (hU b (hAp b hb).symm (hBpost b hb).symm).2.symm
    · intro a ha b hb
      have hAa := hcross a ha A (Or.inl rfl)
      have hBa := hcross a ha B (Or.inr (Or.inl rfl))
      rcases hb with rfl | rfl | hb
      · exact (hU a hAa hBa).1
      · exact (hU a hAa hBa).2
      · exact hcross a ha b (Or.inr (Or.inr hb))
  · intro i hi
    obtain ⟨P, hP, hiP⟩ := h5 i hi
    simp only [List.mem_append, List.mem_cons] at hP
    rcases hP with hP | rfl | rfl | hP
    · exact ⟨P, by simp [hP], hiP⟩
    · have : i ∈ A' ∪ B' := by rw [hun]; exact Finset.mem_union_left _ hiP
      rcases Finset.mem_union.mp this with h | h
      · exact ⟨A', by simp, h⟩
      · exact ⟨B', by simp, h⟩
    · have : i ∈ A' ∪ B' := by rw [hun]; exact Finset.mem_union_right _ hiP
      rcases Finset.mem_union.mp this with h | h
      · exact ⟨A', by simp, h⟩
      · exact ⟨B', by simp, h⟩
    · exact ⟨P, by simp [hP], hiP⟩

def Sep (r : α → ℕ) (A B : Finset α) : Prop := ∀ x ∈ A, ∀ y ∈ B, r x < r y

def Adj (R : Finset α → Finset α → Prop) : List (Finset α) → Prop
  | [] => True
  | [_] => True
  | A :: B :: rest => R A B ∧ Adj R (B :: rest)

theorem adj_or (R : Finset α → Finset α → Prop) : ∀ S : List (Finset α),
    Adj R S ∨ ∃ pre A B post, S = pre ++ A :: B :: post ∧ ¬ R A B := by
  intro S
  induction S with
  | nil => left; trivial
  | cons a l ih =>
    rcases l with _ | ⟨b, rest⟩
    · left; trivial
    · by_cases hab : R a b
      · rcases ih with h | ⟨pre, A, B, post, e, hn⟩
        · left; exact ⟨hab, h⟩
        · right; exact ⟨a :: pre, A, B, post, by simp [e], hn⟩
      · right; exact ⟨[], a, b, rest, rfl, hab⟩

theorem adj_pairwise (r : α → ℕ) : ∀ S : List (Finset α), (∀ P ∈ S, P.Nonempty) →
    Adj (Sep r) S → S.Pairwise (Sep r) := by
  intro S
  induction S with
  | nil => intros; exact List.Pairwise.nil
  | cons a l ih =>
    intro hne hadj
    rcases l with _ | ⟨b, rest⟩
    · exact List.pairwise_singleton _ _
    · obtain ⟨hab, hrest⟩ := hadj
      have ihp := ih (fun P hP => hne P (List.mem_cons_of_mem _ hP)) hrest
      rw [List.pairwise_cons]
      refine ⟨?_, ihp⟩
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact hab
      · have hbc : Sep r b c := (List.pairwise_cons.mp ihp).1 c hc
        obtain ⟨y, hy⟩ := hne b (by simp)
        intro x hx z hz
        exact lt_trans (hab x hx y hy) (hbc y hy z hz)

noncomputable def Psi (N : ℕ) (r : α → ℕ) (S : List (Finset α)) : ℕ := (S.map (fun P => N - mn r P)).sum

theorem mn_lt {r : α → ℕ} {N : ℕ} (hN : ∀ x, r x < N) {P : Finset α} (h : P.Nonempty) :
    mn r P < N := by
  obtain ⟨x, _, e⟩ := exists_mn (r := r) h
  rw [← e]; exact hN x

theorem mn_ne {r : α → ℕ} (hinj : Function.Injective r) {A B : Finset α}
    (hA : A.Nonempty) (hB : B.Nonempty) (hdisj : Disjoint A B) : mn r A ≠ mn r B := by
  obtain ⟨x, hx, ex⟩ := exists_mn (r := r) hA
  obtain ⟨y, hy, ey⟩ := exists_mn (r := r) hB
  intro h
  have : r x = r y := by rw [ex, ey, h]
  have hxy := hinj this
  subst hxy
  exact Finset.disjoint_left.mp hdisj hx hy

instance instTotalMn (r : α → ℕ) : Std.Total (fun A B : Finset α => mn r A ≤ mn r B) :=
  ⟨fun _ _ => le_total _ _⟩

instance instTransMn (r : α → ℕ) : IsTrans (Finset α) (fun A B : Finset α => mn r A ≤ mn r B) :=
  ⟨fun _ _ _ => le_trans⟩

theorem core {r p d : α → ℕ} {N cap : ℕ} {J : Finset α}
    (hinj : Function.Injective r) (hN : ∀ x, r x < N)
    (hp : ∀ x y, r x ≤ r y → p x ≤ p y) (hd : ∀ x y, r x ≤ r y → d x ≤ d y) :
    ∀ (k : ℕ) (S : List (Finset α)), Psi N r S = k → Valid cap J S → Feas p d 0 S →
      S.Pairwise (fun A B => mn r A ≤ mn r B) →
      ∃ S' : List (Finset α), Valid cap J S' ∧ Feas p d 0 S' ∧ S'.Pairwise (Sep r) ∧
        tms p S' ≤ tms p S := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro S hk hv hf hs
  rcases adj_or (Sep r) S with hadj | ⟨pre, A, B, post, rfl, hnot⟩
  · exact ⟨S, hv, hf, adj_pairwise r S hv.1 hadj, le_rfl⟩
  · have hv0 := hv
    obtain ⟨h1, h2, h3, h4, h5⟩ := hv0
    have hAm : A ∈ pre ++ A :: B :: post := by simp
    have hBm : B ∈ pre ++ A :: B :: post := by simp
    have hAne := h1 A hAm
    have hBne := h1 B hBm
    have hdisj : Disjoint A B := by
      have := h4
      simp only [List.pairwise_append, List.pairwise_cons] at this
      exact this.2.1.1 B List.mem_cons_self
    have hsAB : mn r A ≤ mn r B := by
      have := hs
      simp only [List.pairwise_append, List.pairwise_cons] at this
      exact this.2.1.1 B List.mem_cons_self
    have hlt : mn r A < mn r B := lt_of_le_of_ne hsAB (mn_ne hinj hAne hBne hdisj)
    have hcross : ∃ u ∈ A, mn r B < r u := by
      simp only [Sep, not_forall] at hnot
      obtain ⟨x, hx, y, hy, hxy⟩ := hnot
      refine ⟨x, hx, ?_⟩
      have h1 : mn r B ≤ r y := mn_le hy
      have h2 : r x ≠ r y := fun e => by
        have := hinj e
        subst this
        exact Finset.disjoint_left.mp hdisj hx hy
      omega
    have hf' := (feas_append _ _ _).mp hf
    have hFA := hf'.2.1
    have hFB := hf'.2.2.1
    have hFpost := hf'.2.2.2
    obtain ⟨A', B', hA'ne, hB'ne, hA'c, hB'c, hdis, hun, htm, hFA', hFB', hmn⟩ :=
      exchange hinj hp hd hAne hBne (h2 A hAm) (h2 B hBm) hdisj hFA hFB hlt hcross
    have hv'' := valid_replace hv hA'ne hB'ne hA'c hB'c hdis hun
    have hf'' : Feas p d 0 (pre ++ A' :: B' :: post) := by
      rw [feas_append]
      refine ⟨hf'.1, hFA', hFB', feas_mono post ?_ hFpost⟩
      omega
    have htms : tms p (pre ++ A' :: B' :: post) ≤ tms p (pre ++ A :: B :: post) := by
      simp only [tms, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
      omega
    have hpsi : Psi N r (pre ++ A' :: B' :: post) < Psi N r (pre ++ A :: B :: post) := by
      have e1 := mn_lt hN hA'ne
      have e2 := mn_lt hN hB'ne
      have e3 := mn_lt hN hAne
      have e4 := mn_lt hN hBne
      simp only [Psi, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
      omega
    -- sort
    set S' := pre ++ A' :: B' :: post with hS'
    set S'' := List.insertionSort (fun A B : Finset α => mn r A ≤ mn r B) S' with hS''
    have hperm : S''.Perm S' := List.perm_insertionSort _ _
    have hvS'' : Valid cap J S'' := valid_perm hperm.symm hv''
    have hfS'' : Feas p d 0 S'' := feas_sort hd S' hv''.1 0 hf''
    have hsS'' : S''.Pairwise (fun A B : Finset α => mn r A ≤ mn r B) :=
      List.pairwise_insertionSort _ _
    have hpsiS'' : Psi N r S'' = Psi N r S' := by
      simp only [Psi]; exact (hperm.map _).sum_eq
    have htmsS'' : tms p S'' = tms p S' := by
      simp only [tms]; exact (hperm.map _).sum_eq
    obtain ⟨S3, hv3, hf3, hp3, ht3⟩ := ih (Psi N r S'') (by rw [hpsiS'']; omega) S'' rfl
      hvS'' hfS'' hsS''
    exact ⟨S3, hv3, hf3, hp3, by omega⟩

theorem feas_iff {n : ℕ} (p d : Fin n → ℕ) : ∀ (S : List (Finset (Fin n))) (θ : ℕ),
    Feas p d θ S ↔ ∀ (k : ℕ) (hk : k < S.length), ∀ i ∈ S[k],
      θ + ((S.take (k + 1)).map (tm p)).sum ≤ d i := by
  intro S
  induction S with
  | nil => intro θ; simp [Feas]
  | cons P R ih =>
    intro θ
    rw [Feas, ih]
    constructor
    · rintro ⟨h0, h1⟩ k hk i hi
      rcases k with _ | k
      · simp at hi ⊢
        exact h0 i hi
      · have := h1 k (by simpa using hk) i (by simpa using hi)
        simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
        omega
    · intro h
      refine ⟨fun i hi => ?_, fun k hk i hi => ?_⟩
      · have := h 0 (by simp) i (by simpa using hi)
        simpa using this
      · have := h (k + 1) (by simpa using hk) i (by simpa using hi)
        simp only [List.take_succ_cons, List.map_cons, List.sum_cons] at this
        omega

theorem tmax_zero_iff {n : ℕ} (p d : Fin n → ℕ) (S : List (Finset (Fin n))) :
    Tmax p d S = 0 ↔ Feas p d 0 S := by
  rw [feas_iff]
  unfold Tmax
  constructor
  · intro h k hk i hi
    have h1 := (Finset.sup_eq_bot_iff _ _).mp (show _ = (⊥ : ℕ) from h) ⟨k, hk⟩ (Finset.mem_univ _)
    have h2 := (Finset.sup_eq_bot_iff _ _).mp h1 i hi
    have : batchCompletion p S k - d i = 0 := h2
    unfold batchCompletion at this
    have : ((S.take (k + 1)).map (batchTime p)).sum ≤ d i := by omega
    simp only [zero_add]
    exact this
  · intro h
    show _ = (⊥ : ℕ)
    rw [Finset.sup_eq_bot_iff]
    intro k _
    rw [Finset.sup_eq_bot_iff]
    intro i hi
    have := h k.1 k.2 i hi
    simp only [zero_add] at this
    show batchCompletion p S k.1 - d i = 0
    unfold batchCompletion
    have e : ((S.take (k.1 + 1)).map (batchTime p)).sum = ((S.take (k.1 + 1)).map (tm p)).sum := rfl
    rw [e]; omega

theorem makespan_eq {n : ℕ} (p : Fin n → ℕ) (S : List (Finset (Fin n))) :
    makespan p S = tms p S := rfl

theorem reduce {r p d : α → ℕ} {N cap : ℕ} {J : Finset α}
    (hinj : Function.Injective r) (hN : ∀ x, r x < N)
    (hp : ∀ x y, r x ≤ r y → p x ≤ p y) (hd : ∀ x y, r x ≤ r y → d x ≤ d y)
    {S0 : List (Finset α)} (hv : Valid cap J S0) (hf : Feas p d 0 S0) :
    ∃ S' : List (Finset α), Valid cap J S' ∧ Feas p d 0 S' ∧ S'.Pairwise (Sep r) ∧
      tms p S' ≤ tms p S0 := by
  set S1 := List.insertionSort (fun A B : Finset α => mn r A ≤ mn r B) S0 with hS1
  have hperm : S1.Perm S0 := List.perm_insertionSort _ _
  have hv1 : Valid cap J S1 := valid_perm hperm.symm hv
  have hf1 : Feas p d 0 S1 := feas_sort hd S0 hv.1 0 hf
  have hs1 : S1.Pairwise (fun A B : Finset α => mn r A ≤ mn r B) := List.pairwise_insertionSort _ _
  have ht1 : tms p S1 = tms p S0 := by
    simp only [tms]; exact (hperm.map _).sum_eq
  obtain ⟨S', h1, h2, h3, h4⟩ := core (cap := cap) (J := J) hinj hN hp hd _ S1 rfl hv1 hf1 hs1
  exact ⟨S', h1, h2, h3, by omega⟩

theorem sep_cases {r : α → ℕ} {S : List (Finset α)} (hs : S.Pairwise (Sep r)) {P Q : Finset α}
    (hP : P ∈ S) (hQ : Q ∈ S) : P = Q ∨ Sep r P Q ∨ Sep r Q P := by
  obtain ⟨a, ha, rfl⟩ := List.mem_iff_getElem.mp hP
  obtain ⟨b, hb, rfl⟩ := List.mem_iff_getElem.mp hQ
  rcases lt_trichotomy a b with h | h | h
  · right; left; exact List.pairwise_iff_getElem.mp hs a b ha hb h
  · left; subst h; rfl
  · right; right; exact List.pairwise_iff_getElem.mp hs b a hb ha h

theorem consec_of_sep {n cap j : ℕ} {S : List (Finset (Fin n))}
    (hv : Valid cap (jobsUpTo n j) S) (hs : S.Pairwise (Sep (fun i : Fin n => i.val))) :
    IsConsecutive S := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hv
  refine ⟨?_, ?_⟩
  · intro P hP i k l hi hl hij hjl
    have hlJ : l ∈ jobsUpTo n j := h3 P hP hl
    have hkJ : k ∈ jobsUpTo n j := by
      simp only [jobsUpTo, Finset.mem_filter, Finset.mem_univ, true_and] at hlJ ⊢
      exact lt_of_le_of_lt hjl hlJ
    obtain ⟨Q, hQ, hkQ⟩ := h5 k hkJ
    rcases sep_cases hs hP hQ with rfl | h | h
    · exact hkQ
    · have := h l hl k hkQ
      exact absurd hjl (not_le.mpr this)
    · have := h k hkQ i hi
      exact absurd hij (not_le.mpr this)
  · intro a b hab i hi k hk
    have := List.pairwise_iff_getElem.mp hs a b a.2 b.2 hab
    exact this i (by simpa using hi) k (by simpa using hk)

theorem consecutive_optimal_core {n B : ℕ} (hB : 0 < B) (p d : Fin n → ℕ)
    (hd : Monotone d) (hp : Monotone p) (j : ℕ) (hj : j ≤ n)
    (hfeas : ∃ S : List (Finset (Fin n)), IsValid B (jobsUpTo n j) S ∧ Tmax p d S = 0) :
    ∃ S : List (Finset (Fin n)), IsValid B (jobsUpTo n j) S ∧ Tmax p d S = 0 ∧
      IsConsecutive S ∧
      ∀ S' : List (Finset (Fin n)), IsValid B (jobsUpTo n j) S' → Tmax p d S' = 0 →
        makespan p S ≤ makespan p S' := by
  classical
  have hex : ∃ m, ∃ S : List (Finset (Fin n)), IsValid B (jobsUpTo n j) S ∧ Tmax p d S = 0 ∧
      makespan p S = m := by
    obtain ⟨S, h1, h2⟩ := hfeas
    exact ⟨_, S, h1, h2, rfl⟩
  obtain ⟨Sm, hvm, htm, hmm⟩ := Nat.find_spec hex
  have hp' : ∀ x y : Fin n, x.val ≤ y.val → p x ≤ p y := fun x y h => hp (Fin.le_def.mpr h)
  have hd' : ∀ x y : Fin n, x.val ≤ y.val → d x ≤ d y := fun x y h => hd (Fin.le_def.mpr h)
  obtain ⟨S', h1, h2, h3, h4⟩ := reduce (r := fun i : Fin n => i.val) (N := n) (cap := B)
    (J := jobsUpTo n j) Fin.val_injective (fun x => x.2) hp' hd' (S0 := Sm) hvm
    ((tmax_zero_iff p d Sm).mp htm)
  refine ⟨S', h1, (tmax_zero_iff p d S').mpr h2, consec_of_sep h1 h3, ?_⟩
  intro S'' hv'' ht''
  have hmin : Nat.find hex ≤ makespan p S'' := Nat.find_min' hex ⟨S'', hv'', ht'', rfl⟩
  have : makespan p S' ≤ makespan p Sm := h4
  omega

end Core
end BurnInBatch.AgreeTmax

open BurnInBatch.AgreeTmax


theorem solution {n B : ℕ} (hB : 0 < B) (p d : Fin n → ℕ)
    (hd : Monotone d) (hp : Monotone p) (j : ℕ) (hj : j ≤ n)
    (hfeas : ∃ S : List (Finset (Fin n)), IsValid B (jobsUpTo n j) S ∧ Tmax p d S = 0) :
    ∃ S : List (Finset (Fin n)), IsValid B (jobsUpTo n j) S ∧ Tmax p d S = 0 ∧
      IsConsecutive S ∧
      ∀ S' : List (Finset (Fin n)), IsValid B (jobsUpTo n j) S' → Tmax p d S' = 0 →
        makespan p S ≤ makespan p S' := by
  exact Core.consecutive_optimal_core hB p d hd hp j hj hfeas
