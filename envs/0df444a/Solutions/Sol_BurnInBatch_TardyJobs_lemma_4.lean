-- Prove2me | solution 1 for BurnInBatch.TardyJobs.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T01:55:17.496446+00:00
-- url     : https://prove2.me/submissions/392f9957-c2a3-4768-b51f-f57a15378e48

import Mathlib
import Definitions.Def_BurnInBatch_TardyJobs_Model



namespace BurnInBatch.TardyJobs

open Classical

section Infra
variable {n : ℕ}

def stp (p r : Fin n → ℕ) (t : ℕ) (P : Finset (Fin n)) : ℕ :=
  max t (P.sup r) + P.sup p

theorem finish_cons (p r : Fin n → ℕ) (P : Finset (Fin n)) (S : List (Finset (Fin n))) (t : ℕ) :
    finish p r (P :: S) t = finish p r S (stp p r t P) := rfl

theorem aux_cons (p r : Fin n → ℕ) (j : Fin n) (P : Finset (Fin n)) (S : List (Finset (Fin n))) (t : ℕ) :
    jobCompletionAux p r j (P :: S) t =
      if j ∈ P then stp p r t P else jobCompletionAux p r j S (stp p r t P) := rfl

def OT (p r d : Fin n → ℕ) (Q : Fin n → Prop) : List (Finset (Fin n)) → ℕ → Prop
  | [], _ => True
  | P :: S, t => (∀ j ∈ P, Q j → stp p r t P ≤ d j) ∧ OT p r d Q S (stp p r t P)

theorem stp_mono (p r : Fin n → ℕ) {t t' : ℕ} {P P' : Finset (Fin n)} (ht : t ≤ t') (hP : P ⊆ P') :
    stp p r t P ≤ stp p r t' P' :=
  Nat.add_le_add (max_le_max ht (Finset.sup_mono hP)) (Finset.sup_mono hP)

theorem le_stp (p r : Fin n → ℕ) (t : ℕ) (P : Finset (Fin n)) : t ≤ stp p r t P :=
  (le_max_left _ _).trans (Nat.le_add_right _ _)

theorem finish_ge (p r : Fin n → ℕ) (S : List (Finset (Fin n))) : ∀ t, t ≤ finish p r S t := by
  induction S with
  | nil => intro t; exact le_rfl
  | cons P S ih => intro t; rw [finish_cons]; exact (le_stp p r t P).trans (ih _)

theorem finish_mono (p r : Fin n → ℕ) (S : List (Finset (Fin n))) :
    ∀ {t t'}, t ≤ t' → finish p r S t ≤ finish p r S t' := by
  induction S with
  | nil => intro t t' h; exact h
  | cons P S ih => intro t t' h; rw [finish_cons, finish_cons]; exact ih (stp_mono p r h le_rfl)

theorem finish_append (p r : Fin n → ℕ) (S1 S2 : List (Finset (Fin n))) :
    ∀ t, finish p r (S1 ++ S2) t = finish p r S2 (finish p r S1 t) := by
  induction S1 with
  | nil => intro t; rfl
  | cons P S ih => intro t; simp only [List.cons_append, finish_cons]; exact ih _

theorem OT_append (p r d : Fin n → ℕ) (Q : Fin n → Prop) (S1 S2 : List (Finset (Fin n))) :
    ∀ t, OT p r d Q (S1 ++ S2) t ↔ OT p r d Q S1 t ∧ OT p r d Q S2 (finish p r S1 t) := by
  induction S1 with
  | nil => intro t; simp [OT, finish]
  | cons P S ih =>
    intro t
    simp only [List.cons_append, OT, finish_cons, ih]
    tauto

theorem OT_anti (p r d : Fin n → ℕ) (Q : Fin n → Prop) (S : List (Finset (Fin n))) :
    ∀ {t t'}, t' ≤ t → OT p r d Q S t → OT p r d Q S t' := by
  induction S with
  | nil => intro t t' _ _; trivial
  | cons P S ih =>
    intro t t' h hO
    exact ⟨fun j hj hQ => (stp_mono p r h le_rfl).trans (hO.1 j hj hQ),
      ih (stp_mono p r h le_rfl) hO.2⟩

theorem OT_shrink (p r d : Fin n → ℕ) (Q : Fin n → Prop) (S' : List (Finset (Fin n))) :
    ∀ (S : List (Finset (Fin n))) {t' t : ℕ}, List.Forall₂ (fun a b => a ⊆ b) S' S → t' ≤ t →
      (∀ P ∈ S', ∀ j ∈ P, Q j) → OT p r d Q S t → OT p r d (fun _ => True) S' t' := by
  induction S' with
  | nil => intros; trivial
  | cons P' S' ih =>
    intro S t' t hF ht hQ hO
    cases hF with
    | cons hPb hrest =>
      rename_i P S0
      refine ⟨fun j hj _ => ?_, ih S0 hrest (stp_mono p r ht hPb) (fun P hP j hj => hQ P (List.mem_cons_of_mem _ hP) j hj) hO.2⟩
      exact (stp_mono p r ht hPb).trans (hO.1 j (hPb hj) (hQ P' (List.mem_cons_self) j hj))

theorem aux_iff_OT (p r d : Fin n → ℕ) (Q : Fin n → Prop) (S : List (Finset (Fin n))) :
    ∀ t, S.Pairwise Disjoint →
      ((∀ j, (∃ P ∈ S, j ∈ P) → Q j → jobCompletionAux p r j S t ≤ d j) ↔ OT p r d Q S t) := by
  induction S with
  | nil => intro t _; simp [OT]
  | cons P S ih =>
    intro t hdis
    rw [List.pairwise_cons] at hdis
    obtain ⟨hPS, hS⟩ := hdis
    have key : ∀ j, (∃ P' ∈ S, j ∈ P') → j ∉ P := by
      intro j ⟨P', hP', hj⟩ hjP
      exact Finset.disjoint_left.mp (hPS P' hP') hjP hj
    rw [OT, ← ih _ hS]
    constructor
    · intro h
      refine ⟨fun j hj hQ => ?_, fun j hj hQ => ?_⟩
      · have := h j ⟨P, List.mem_cons_self, hj⟩ hQ
        rwa [aux_cons, if_pos hj] at this
      · have := h j (by obtain ⟨P', hP', hj'⟩ := hj; exact ⟨P', List.mem_cons_of_mem _ hP', hj'⟩) hQ
        rwa [aux_cons, if_neg (key j hj)] at this
    · rintro ⟨h1, h2⟩ j ⟨P', hP', hj⟩ hQ
      rw [aux_cons]
      by_cases hjP : j ∈ P
      · rw [if_pos hjP]; exact h1 j hjP hQ
      · rw [if_neg hjP]
        have : ∃ P'' ∈ S, j ∈ P'' := by
          rcases List.mem_cons.mp hP' with rfl | h
          · exact absurd hj hjP
          · exact ⟨P', h, hj⟩
        exact h2 j this hQ

theorem OT_filter_nonempty (p r d : Fin n → ℕ) (Q : Fin n → Prop) (S : List (Finset (Fin n))) :
    ∀ t, OT p r d Q (S.filter (fun P => decide P.Nonempty)) t ↔ OT p r d Q S t := by
  induction S with
  | nil => intro t; simp
  | cons P S ih =>
    intro t
    by_cases hP : P.Nonempty
    · simp only [List.filter_cons, decide_eq_true hP, if_true, OT]
      rw [ih]
    · have hE : P = ∅ := Finset.not_nonempty_iff_eq_empty.mp hP
      subst hE
      have : stp p r t ∅ = t := by simp [stp]
      simp only [List.filter_cons, Finset.not_nonempty_empty, decide_false, Bool.false_eq_true, if_false, OT, this]
      rw [ih]
      simp

def U (L : List (Finset (Fin n))) : Finset (Fin n) := L.foldr (· ∪ ·) ∅

theorem mem_U {L : List (Finset (Fin n))} {j : Fin n} : j ∈ U L ↔ ∃ P ∈ L, j ∈ P := by
  induction L with
  | nil => simp [U]
  | cons P L ih =>
    simp only [U, List.foldr_cons, Finset.mem_union] at ih ⊢
    rw [ih]
    simp

theorem U_append (A C : List (Finset (Fin n))) : U (A ++ C) = U A ∪ U C := by
  ext j; simp only [Finset.mem_union, mem_U, List.mem_append]
  constructor
  · rintro ⟨P, hP | hP, hj⟩
    · exact Or.inl ⟨P, hP, hj⟩
    · exact Or.inr ⟨P, hP, hj⟩
  · rintro (⟨P, hP, hj⟩ | ⟨P, hP, hj⟩)
    · exact ⟨P, Or.inl hP, hj⟩
    · exact ⟨P, Or.inr hP, hj⟩

theorem U_cons (P : Finset (Fin n)) (L : List (Finset (Fin n))) : U (P :: L) = P ∪ U L := rfl

def Good (B : ℕ) (p r d : Fin n → ℕ) (L : List (Finset (Fin n))) : Prop :=
  (∀ P ∈ L, P.Nonempty ∧ P.card ≤ B) ∧ L.Pairwise Disjoint ∧ OT p r d (fun _ => True) L 0

theorem aux_append_left (p r : Fin n → ℕ) (j : Fin n) :
    ∀ (A T : List (Finset (Fin n))) (t : ℕ), (∃ P ∈ A, j ∈ P) →
      jobCompletionAux p r j (A ++ T) t = jobCompletionAux p r j A t := by
  intro A
  induction A with
  | nil => intro T t h; obtain ⟨P, hP, _⟩ := h; simp at hP
  | cons P A ih =>
    intro T t h
    by_cases hj : j ∈ P
    · simp only [List.cons_append, aux_cons, if_pos hj]
    · simp only [List.cons_append, aux_cons, if_neg hj]
      apply ih
      obtain ⟨P', hP', hj'⟩ := h
      rcases List.mem_cons.mp hP' with rfl | h
      · exact absurd hj' hj
      · exact ⟨P', h, hj'⟩

end Infra

section Reduction
variable {n : ℕ}

theorem good_of_valid (B : ℕ) (p r d : Fin n → ℕ) (S : List (Finset (Fin n))) (hS : ValidSchedule B S) :
    ∃ L, Good B p r d L ∧ ∀ j, j ∈ U L ↔ jobCompletion p r S j ≤ d j := by
  obtain ⟨hv, hdis, hcov⟩ := hS
  let Q : Fin n → Prop := fun j => jobCompletion p r S j ≤ d j
  have hOT : OT p r d Q S 0 := (aux_iff_OT p r d Q S 0 hdis).mp (fun j _ hj => hj)
  let S' := S.map (fun P => P.filter Q)
  have hF : List.Forall₂ (fun a b => a ⊆ b) S' S := by
    simp [S', List.forall₂_map_left_iff, List.forall₂_same, Finset.filter_subset]
  have hOT' : OT p r d (fun _ => True) S' 0 :=
    OT_shrink p r d Q S' S hF le_rfl (fun P hP j hj => by
      obtain ⟨P0, _, rfl⟩ := List.mem_map.mp hP
      exact (Finset.mem_filter.mp hj).2) hOT
  refine ⟨S'.filter (fun P => decide P.Nonempty), ⟨?_, ?_, (OT_filter_nonempty p r d _ S' 0).mpr hOT'⟩, ?_⟩
  · intro P hP
    obtain ⟨hP1, hP2⟩ := List.mem_filter.mp hP
    obtain ⟨P0, hP0, rfl⟩ := List.mem_map.mp hP1
    exact ⟨by simpa using hP2, (Finset.card_filter_le _ _).trans (hv P0 hP0).2⟩
  · have h1 : S'.Pairwise Disjoint :=
      List.Pairwise.map (fun P => P.filter Q) (fun a b hab =>
        Finset.disjoint_of_subset_left (Finset.filter_subset _ _)
          (Finset.disjoint_of_subset_right (Finset.filter_subset _ _) hab)) hdis
    exact h1.sublist (List.filter_sublist)
  · intro j
    rw [mem_U]
    constructor
    · rintro ⟨P, hP, hj⟩
      obtain ⟨hP1, hP2⟩ := List.mem_filter.mp hP
      obtain ⟨P0, _, rfl⟩ := List.mem_map.mp hP1
      exact (Finset.mem_filter.mp hj).2
    · intro hj
      obtain ⟨P0, hP0, hjP0⟩ := hcov j
      refine ⟨P0.filter Q, List.mem_filter.mpr ⟨List.mem_map.mpr ⟨P0, hP0, rfl⟩, ?_⟩,
        Finset.mem_filter.mpr ⟨hjP0, hj⟩⟩
      simpa using ⟨j, Finset.mem_filter.mpr ⟨hjP0, hj⟩⟩

noncomputable def singles (O : Finset (Fin n)) : List (Finset (Fin n)) := (Oᶜ).toList.map (fun x => {x})

theorem mem_singles {O : Finset (Fin n)} {P : Finset (Fin n)} : P ∈ singles O ↔ ∃ x, x ∉ O ∧ P = {x} := by
  simp [singles]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩

theorem U_singles (O : Finset (Fin n)) : U (singles O) = Oᶜ := by
  ext j
  rw [mem_U]
  constructor
  · rintro ⟨P, hP, hj⟩
    obtain ⟨x, hx, rfl⟩ := mem_singles.mp hP
    rw [Finset.mem_singleton] at hj
    subst hj; simpa using hx
  · intro hj
    exact ⟨{j}, mem_singles.mpr ⟨j, by simpa using hj, rfl⟩, Finset.mem_singleton_self j⟩

theorem singles_pairwise (O : Finset (Fin n)) : (singles O).Pairwise Disjoint := by
  have : (Oᶜ).toList.Pairwise (· ≠ ·) := Finset.nodup_toList _
  exact List.Pairwise.map (fun x : Fin n => ({x} : Finset (Fin n))) (fun a b h => Finset.disjoint_singleton.mpr h) this

theorem valid_append_singles (B : ℕ) (hB : 0 < B) (p r d : Fin n → ℕ) (L : List (Finset (Fin n)))
    (hL : Good B p r d L) : ValidSchedule B (L ++ singles (U L)) := by
  obtain ⟨hv, hdis, _⟩ := hL
  refine ⟨?_, ?_, ?_⟩
  · intro P hP
    rcases List.mem_append.mp hP with h | h
    · exact hv P h
    · obtain ⟨x, _, rfl⟩ := mem_singles.mp h
      exact ⟨Finset.singleton_nonempty x, by rw [Finset.card_singleton]; exact hB⟩
  · rw [List.pairwise_append]
    refine ⟨hdis, singles_pairwise _, ?_⟩
    intro P hP Q hQ
    obtain ⟨x, hx, rfl⟩ := mem_singles.mp hQ
    exact Finset.disjoint_singleton_right.mpr (fun hxP => hx (mem_U.mpr ⟨P, hP, hxP⟩))
  · intro j
    by_cases hj : j ∈ U L
    · obtain ⟨P, hP, hjP⟩ := mem_U.mp hj
      exact ⟨P, List.mem_append.mpr (Or.inl hP), hjP⟩
    · exact ⟨{j}, List.mem_append.mpr (Or.inr (mem_singles.mpr ⟨j, hj, rfl⟩)), Finset.mem_singleton_self j⟩

theorem completion_L (B : ℕ) (p r d : Fin n → ℕ) (L T : List (Finset (Fin n))) (hL : Good B p r d L) :
    ∀ j ∈ U L, jobCompletion p r (L ++ T) j ≤ d j := by
  intro j hj
  obtain ⟨hv, hdis, hOT⟩ := hL
  have hc := (aux_iff_OT p r d (fun _ => True) L 0 hdis).mpr hOT
  have := aux_append_left p r j L T 0 (mem_U.mp hj)
  unfold jobCompletion
  rw [this]
  exact hc j (mem_U.mp hj) trivial

/-- number of on-time jobs -/
def onTime (p r d : Fin n → ℕ) (S : List (Finset (Fin n))) : Finset (Fin n) :=
  Finset.univ.filter (fun j => jobCompletion p r S j ≤ d j)

theorem tardyCount_eq (p r d : Fin n → ℕ) (S : List (Finset (Fin n))) :
    tardyCount p r d S + (onTime p r d S).card = n := by
  unfold tardyCount onTime
  have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun j => d j < jobCompletion p r S j)
  simp only [not_lt] at this
  simpa using this

def FS (B : ℕ) (p r d : Fin n → ℕ) (O : Finset (Fin n)) : Prop :=
  ∃ L, Good B p r d L ∧ U L = O

theorem FS_empty (B : ℕ) (p r d : Fin n → ℕ) : FS B p r d ∅ :=
  ⟨[], ⟨by simp, List.Pairwise.nil, trivial⟩, rfl⟩

theorem exists_max_FS (B : ℕ) (p r d : Fin n → ℕ) :
    ∃ O, FS B p r d O ∧ ∀ O', FS B p r d O' → O'.card ≤ O.card := by
  obtain ⟨O, hO, hmax⟩ := Finset.exists_max_image (Finset.univ.filter (fun O => FS B p r d O))
    Finset.card ⟨∅, by simpa using FS_empty B p r d⟩
  exact ⟨O, (Finset.mem_filter.mp hO).2, fun O' h => hmax O' (by simpa using h)⟩

theorem minTardy_eq (B : ℕ) (hB : 0 < B) (p r d : Fin n → ℕ) (O : Finset (Fin n))
    (hO : FS B p r d O) (hmax : ∀ O', FS B p r d O' → O'.card ≤ O.card) :
    minTardy B p r d = n - O.card := by
  obtain ⟨L, hL, rfl⟩ := hO
  have hS0 := valid_append_singles B hB p r d L hL
  have h1 : tardyCount p r d (L ++ singles (U L)) ≤ n - (U L).card := by
    have := tardyCount_eq p r d (L ++ singles (U L))
    have hsub : U L ⊆ onTime p r d (L ++ singles (U L)) := by
      intro j hj
      simp only [onTime, Finset.mem_filter, Finset.mem_univ, true_and]
      exact completion_L B p r d L _ hL j hj
    have := Finset.card_le_card hsub
    omega
  have hne : { v : ℕ | ∃ S : List (Finset (Fin n)), ValidSchedule B S ∧ tardyCount p r d S = v }.Nonempty :=
    ⟨_, _, hS0, rfl⟩
  have h2 : minTardy B p r d ≤ tardyCount p r d (L ++ singles (U L)) :=
    Nat.sInf_le ⟨_, hS0, rfl⟩
  have h3 := Nat.sInf_mem hne
  obtain ⟨S, hS, hSeq⟩ := h3
  have hmt : minTardy B p r d = tardyCount p r d S := hSeq.symm
  obtain ⟨L', hL', hU'⟩ := good_of_valid B p r d S hS
  have hon : U L' = onTime p r d S := by
    ext j; rw [hU']; simp [onTime]
  have hcard := hmax _ ⟨L', hL', rfl⟩
  have := tardyCount_eq p r d S
  rw [hon] at hcard
  omega

end Reduction

section Sorting
variable {n : ℕ}

theorem sup_equal (p0 : ℕ) {P : Finset (Fin n)} (hP : P.Nonempty) : P.sup (equalTime p0) = p0 := by
  unfold equalTime
  exact Finset.sup_const hP p0

def Sorted (ρ : Fin n → ℕ) (L : List (Finset (Fin n))) : Prop :=
  L.Pairwise (fun P Q => ∀ i ∈ P, ∀ j ∈ Q, ρ i < ρ j)

def wt (ρ : Fin n → ℕ) (P : Finset (Fin n)) : ℕ := ∑ x ∈ P, ρ x

def phi (ρ : Fin n → ℕ) : List (Finset (Fin n)) → ℕ → ℕ
  | [], _ => 0
  | P :: L, c => c * wt ρ P + phi ρ L (c + 1)

theorem phi_append (ρ : Fin n → ℕ) (A X : List (Finset (Fin n))) :
    ∀ c, phi ρ (A ++ X) c = phi ρ A c + phi ρ X (c + A.length) := by
  induction A with
  | nil => intro c; simp [phi]
  | cons P A ih =>
    intro c
    rw [List.cons_append, phi, phi, ih, List.length_cons]
    have : c + 1 + A.length = c + (A.length + 1) := by omega
    rw [this]; ring

theorem phi_mid (ρ : Fin n → ℕ) (A M C : List (Finset (Fin n))) (P Q : Finset (Fin n)) (c : ℕ) :
    phi ρ (A ++ (P :: (M ++ (Q :: C)))) c =
      phi ρ A c + (c + A.length) * wt ρ P + phi ρ M (c + A.length + 1)
        + (c + A.length + 1 + M.length) * wt ρ Q + phi ρ C (c + A.length + 1 + M.length + 1) := by
  rw [phi_append, phi, phi_append, phi]
  ring

theorem wt_swap (ρ : Fin n → ℕ) (X : Finset (Fin n)) (a b : Fin n) (ha : a ∈ X) (hb : b ∉ X) :
    wt ρ (X.image (Equiv.swap a b)) + ρ a = wt ρ X + ρ b := by
  unfold wt
  rw [Finset.sum_image (fun x _ y _ h => (Equiv.swap a b).injective h)]
  rw [← Finset.add_sum_erase X _ ha, ← Finset.add_sum_erase X ρ ha]
  rw [Equiv.swap_apply_left]
  have : ∑ x ∈ X.erase a, ρ ((Equiv.swap a b) x) = ∑ x ∈ X.erase a, ρ x := by
    apply Finset.sum_congr rfl
    intro x hx
    have hxa : x ≠ a := Finset.ne_of_mem_erase hx
    have hxb : x ≠ b := fun h => hb (h ▸ Finset.mem_of_mem_erase hx)
    rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]
  rw [this]; ring

theorem mem_image_swap {a b x : Fin n} {X : Finset (Fin n)} :
    x ∈ X.image (Equiv.swap a b) ↔ (Equiv.swap a b) x ∈ X := by
  constructor
  · rintro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    simpa using hy
  · intro h
    exact Finset.mem_image.mpr ⟨_, h, by simp⟩

theorem image_swap_fix {a b : Fin n} {X : Finset (Fin n)} (ha : a ∉ X) (hb : b ∉ X) :
    X.image (Equiv.swap a b) = X := by
  ext x
  rw [mem_image_swap]
  by_cases hxa : x = a
  · subst hxa; simp [ha, hb]
  · by_cases hxb : x = b
    · subst hxb; simp [ha, hb]
    · rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]

theorem sorted_decomp {α : Type*} (a b : α) : ∀ (L : List α), [a, b].Sublist L →
    ∃ A M C, L = A ++ (a :: (M ++ (b :: C))) := by
  intro L
  induction L with
  | nil => intro h; simp at h
  | cons x L ih =>
    intro h
    rcases List.sublist_cons_iff.mp h with h1 | ⟨r, hr, h2⟩
    · obtain ⟨A, M, C, rfl⟩ := ih h1
      exact ⟨x :: A, M, C, by simp⟩
    · obtain ⟨hax, rfl⟩ := List.cons.inj hr
      subst hax
      have : b ∈ L := by
        have := h2.subset (List.mem_cons_self)
        simpa using this
      obtain ⟨s, t, rfl⟩ := List.append_of_mem this
      exact ⟨[], s, t, by simp⟩

end Sorting

section Swap
variable {n : ℕ}

theorem stp_eq (p0 : ℕ) (r : Fin n → ℕ) (t : ℕ) {X : Finset (Fin n)} (hX : X.Nonempty) :
    stp (equalTime p0) r t X = max t (X.sup r) + p0 := by
  unfold stp; rw [sup_equal p0 hX]

theorem disj_facts {A M C : List (Finset (Fin n))} {P Q : Finset (Fin n)}
    (h : (A ++ (P :: (M ++ (Q :: C)))).Pairwise Disjoint) :
    Disjoint P Q ∧ (∀ X ∈ A, Disjoint X P) ∧ (∀ X ∈ A, Disjoint X Q) ∧ (∀ X ∈ M, Disjoint P X) ∧
    (∀ X ∈ M, Disjoint X Q) ∧ (∀ X ∈ C, Disjoint P X) ∧ (∀ X ∈ C, Disjoint Q X) := by
  rw [List.pairwise_append] at h
  obtain ⟨hA, hrest, hcross⟩ := h
  rw [List.pairwise_cons] at hrest
  obtain ⟨hP_all, hrest2⟩ := hrest
  rw [List.pairwise_append] at hrest2
  obtain ⟨hM, hQC, hMQC⟩ := hrest2
  rw [List.pairwise_cons] at hQC
  exact ⟨hP_all Q (by simp), fun X hX => hcross X hX P (by simp), fun X hX => hcross X hX Q (by simp),
    fun X hX => hP_all X (by simp [hX]), fun X hX => hMQC X hX Q (by simp),
    fun X hX => hP_all X (by simp [hX]), fun X hX => hQC.1 X hX⟩

theorem swap_good (B p0 : ℕ) (r d : Fin n → ℕ) (ρ : Fin n → ℕ)
    (hρ : ∀ a b, ρ a < ρ b → r a ≤ r b ∧ d a ≤ d b)
    (A M C : List (Finset (Fin n))) (P Q : Finset (Fin n)) (i j : Fin n)
    (hL : Good B (equalTime p0) r d (A ++ (P :: (M ++ (Q :: C)))))
    (hi : i ∈ P) (hj : j ∈ Q) (hlt : ρ j < ρ i) :
    Good B (equalTime p0) r d
      (A ++ ((P.image (Equiv.swap i j)) :: (M ++ ((Q.image (Equiv.swap i j)) :: C)))) ∧
    U (A ++ ((P.image (Equiv.swap i j)) :: (M ++ ((Q.image (Equiv.swap i j)) :: C))))
      = U (A ++ (P :: (M ++ (Q :: C)))) := by
  obtain ⟨hv, hdis, hOT⟩ := hL
  obtain ⟨hPQ, hAP, hAQ, hPM, hMQ, hPC, hQC⟩ := disj_facts hdis
  have hjP : j ∉ P := fun h => Finset.disjoint_left.mp hPQ h hj
  have hiQ : i ∉ Q := fun h => Finset.disjoint_left.mp hPQ hi h
  have hij : i ≠ j := fun h => hjP (h ▸ hi)
  have hfA : A.map (fun X => X.image (Equiv.swap i j)) = A := by
    rw [List.map_congr_left (g := id)]
    · exact List.map_id _
    · intro X hX
      exact image_swap_fix (Finset.disjoint_right.mp (hAP X hX) hi) (Finset.disjoint_right.mp (hAQ X hX) hj)
  have hfM : M.map (fun X => X.image (Equiv.swap i j)) = M := by
    rw [List.map_congr_left (g := id)]
    · exact List.map_id _
    · intro X hX
      exact image_swap_fix (Finset.disjoint_left.mp (hPM X hX) hi) (Finset.disjoint_right.mp (hMQ X hX) hj)
  have hfC : C.map (fun X => X.image (Equiv.swap i j)) = C := by
    rw [List.map_congr_left (g := id)]
    · exact List.map_id _
    · intro X hX
      exact image_swap_fix (Finset.disjoint_left.mp (hPC X hX) hi) (Finset.disjoint_left.mp (hQC X hX) hj)
  have hmap : (A ++ (P :: (M ++ (Q :: C)))).map (fun X => X.image (Equiv.swap i j)) =
      A ++ ((P.image (Equiv.swap i j)) :: (M ++ ((Q.image (Equiv.swap i j)) :: C))) := by
    simp only [List.map_append, List.map_cons, hfA, hfM, hfC]
  have hPne : P.Nonempty := (hv P (by simp)).1
  have hQne : Q.Nonempty := (hv Q (by simp)).1
  have hP'ne : (P.image (Equiv.swap i j)).Nonempty := hPne.image _
  have hQ'ne : (Q.image (Equiv.swap i j)).Nonempty := hQne.image _
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [← hmap]
    intro X hX
    obtain ⟨Y, hY, rfl⟩ := List.mem_map.mp hX
    exact ⟨(hv Y hY).1.image _, by rw [Finset.card_image_of_injective _ (Equiv.swap i j).injective]; exact (hv Y hY).2⟩
  · rw [← hmap]
    exact List.Pairwise.map (fun X : Finset (Fin n) => X.image (Equiv.swap i j))
      (fun a b hab => (Finset.disjoint_image (Equiv.swap i j).injective).mpr hab) hdis
  · -- OT
    have hOT1 := hOT
    rw [OT_append] at hOT1
    obtain ⟨hOA, hOrest⟩ := hOT1
    simp only [OT] at hOrest
    obtain ⟨hP_on, hOrest⟩ := hOrest
    rw [OT_append] at hOrest
    obtain ⟨hOM, hOQC⟩ := hOrest
    simp only [OT] at hOQC
    obtain ⟨hQ_on, hOC⟩ := hOQC
    -- numeric facts
    have hRP : (P.image (Equiv.swap i j)).sup r ≤ P.sup r := by
      rw [Finset.sup_image]
      apply Finset.sup_le
      intro y hy
      by_cases hyi : y = i
      · simp only [Function.comp, hyi, Equiv.swap_apply_left]
        exact ((hρ _ _ hlt).1).trans (Finset.le_sup hi)
      · have hyj : y ≠ j := fun h => hjP (h ▸ hy)
        simp only [Function.comp, Equiv.swap_apply_of_ne_of_ne hyi hyj]
        exact Finset.le_sup hy
    have hRQ : (Q.image (Equiv.swap i j)).sup r ≤ max (P.sup r) (Q.sup r) := by
      rw [Finset.sup_image]
      apply Finset.sup_le
      intro y hy
      by_cases hyj : y = j
      · simp only [Function.comp, hyj, Equiv.swap_apply_right]
        exact (Finset.le_sup hi).trans (le_max_left _ _)
      · have hyi : y ≠ i := fun h => hiQ (h ▸ hy)
        simp only [Function.comp, Equiv.swap_apply_of_ne_of_ne hyi hyj]
        exact (Finset.le_sup hy).trans (le_max_right _ _)
    have e1 : stp (equalTime p0) r (finish (equalTime p0) r A 0) P
        = max (finish (equalTime p0) r A 0) (P.sup r) + p0 := stp_eq p0 r _ hPne
    have e1' : stp (equalTime p0) r (finish (equalTime p0) r A 0) (P.image (Equiv.swap i j))
        = max (finish (equalTime p0) r A 0) ((P.image (Equiv.swap i j)).sup r) + p0 := stp_eq p0 r _ hP'ne
    have h1 : stp (equalTime p0) r (finish (equalTime p0) r A 0) (P.image (Equiv.swap i j))
        ≤ stp (equalTime p0) r (finish (equalTime p0) r A 0) P := by
      rw [e1, e1']; omega
    have hM1 : stp (equalTime p0) r (finish (equalTime p0) r A 0) P ≤
        finish (equalTime p0) r M (stp (equalTime p0) r (finish (equalTime p0) r A 0) P) :=
      finish_ge _ _ _ _
    have hM' : finish (equalTime p0) r M (stp (equalTime p0) r (finish (equalTime p0) r A 0) (P.image (Equiv.swap i j)))
        ≤ finish (equalTime p0) r M (stp (equalTime p0) r (finish (equalTime p0) r A 0) P) :=
      finish_mono _ _ M h1
    have e2 : stp (equalTime p0) r (finish (equalTime p0) r M (stp (equalTime p0) r (finish (equalTime p0) r A 0) P)) Q
        = max (finish (equalTime p0) r M (stp (equalTime p0) r (finish (equalTime p0) r A 0) P)) (Q.sup r) + p0 :=
      stp_eq p0 r _ hQne
    have e2' : stp (equalTime p0) r (finish (equalTime p0) r M (stp (equalTime p0) r (finish (equalTime p0) r A 0) (P.image (Equiv.swap i j)))) (Q.image (Equiv.swap i j))
        = max (finish (equalTime p0) r M (stp (equalTime p0) r (finish (equalTime p0) r A 0) (P.image (Equiv.swap i j)))) ((Q.image (Equiv.swap i j)).sup r) + p0 :=
      stp_eq p0 r _ hQ'ne
    have h2 : stp (equalTime p0) r (finish (equalTime p0) r M (stp (equalTime p0) r (finish (equalTime p0) r A 0) (P.image (Equiv.swap i j)))) (Q.image (Equiv.swap i j))
        ≤ stp (equalTime p0) r (finish (equalTime p0) r M (stp (equalTime p0) r (finish (equalTime p0) r A 0) P)) Q := by
      rw [e2, e2']; omega
    have hM2 := le_stp (equalTime p0) r (finish (equalTime p0) r M (stp (equalTime p0) r (finish (equalTime p0) r A 0) P)) Q
    rw [OT_append]
    refine ⟨hOA, ?_⟩
    simp only [OT]
    refine ⟨?_, ?_⟩
    · intro x hx _
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      by_cases hyi : y = i
      · rw [hyi, Equiv.swap_apply_left]
        exact h1.trans (hM1.trans (hM2.trans (hQ_on j hj trivial)))
      · have hyj : y ≠ j := fun h => hjP (h ▸ hy)
        rw [Equiv.swap_apply_of_ne_of_ne hyi hyj]
        exact h1.trans (hP_on y hy trivial)
    · rw [OT_append]
      refine ⟨OT_anti _ _ _ _ _ h1 hOM, ?_⟩
      simp only [OT]
      refine ⟨?_, OT_anti _ _ _ _ _ h2 hOC⟩
      intro x hx _
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      by_cases hyj : y = j
      · rw [hyj, Equiv.swap_apply_right]
        exact h2.trans ((hQ_on j hj trivial).trans (hρ _ _ hlt).2)
      · have hyi : y ≠ i := fun h => hiQ (h ▸ hy)
        rw [Equiv.swap_apply_of_ne_of_ne hyi hyj]
        exact h2.trans (hQ_on y hy trivial)
  · have hPQ' : ∀ x, (x ∈ P.image (Equiv.swap i j) ∨ x ∈ Q.image (Equiv.swap i j)) ↔ (x ∈ P ∨ x ∈ Q) := by
      intro x
      rw [mem_image_swap, mem_image_swap]
      by_cases hxi : x = i
      · rw [hxi, Equiv.swap_apply_left]; simp [hi, hj]
      · by_cases hxj : x = j
        · rw [hxj, Equiv.swap_apply_right]; simp [hi, hj]
        · rw [Equiv.swap_apply_of_ne_of_ne hxi hxj]
    ext x
    simp only [U_append, U_cons, Finset.mem_union]
    have := hPQ' x
    constructor <;> intro h <;> tauto

end Swap

section SortMain
variable {n : ℕ}

theorem disj_U {P : Finset (Fin n)} {L : List (Finset (Fin n))} (h : ∀ X ∈ L, Disjoint P X) :
    Disjoint P (U L) := by
  rw [Finset.disjoint_left]
  intro x hx hxU
  obtain ⟨X, hX, hxX⟩ := mem_U.mp hxU
  exact Finset.disjoint_left.mp (h X hX) hx hxX

theorem length_le_card (L : List (Finset (Fin n))) (hne : ∀ P ∈ L, P.Nonempty)
    (hdis : L.Pairwise Disjoint) : L.length ≤ (U L).card := by
  induction L with
  | nil => simp
  | cons P L ih =>
    rw [List.pairwise_cons] at hdis
    have hd : Disjoint P (U L) := disj_U hdis.1
    rw [U_cons, Finset.card_union_of_disjoint hd]
    have := ih (fun X hX => hne X (List.mem_cons_of_mem _ hX)) hdis.2
    have h1 := (hne P List.mem_cons_self).card_pos
    simp only [List.length_cons]; omega

theorem phi_le (ρ : Fin n → ℕ) (L : List (Finset (Fin n))) (hdis : L.Pairwise Disjoint) :
    ∀ c, phi ρ L c ≤ (c + L.length) * ∑ x ∈ U L, ρ x := by
  induction L with
  | nil => intro c; simp [phi]
  | cons P L ih =>
    intro c
    rw [List.pairwise_cons] at hdis
    have hd : Disjoint P (U L) := disj_U hdis.1
    rw [phi, U_cons, Finset.sum_union hd, List.length_cons]
    have := ih hdis.2 (c + 1)
    have e : wt ρ P = ∑ x ∈ P, ρ x := rfl
    rw [e]
    nlinarith [Nat.zero_le (∑ x ∈ P, ρ x), Nat.zero_le (∑ x ∈ U L, ρ x), Nat.zero_le (L.length * ∑ x ∈ P, ρ x)]

theorem phi_bound (ρ : Fin n → ℕ) (L : List (Finset (Fin n))) (hne : ∀ P ∈ L, P.Nonempty)
    (hdis : L.Pairwise Disjoint) : phi ρ L 1 ≤ (1 + n) * ∑ x ∈ U L, ρ x := by
  have h1 := phi_le ρ L hdis 1
  have h2 := length_le_card L hne hdis
  have h3 : (U L).card ≤ n := by simpa using Finset.card_le_univ (U L)
  exact h1.trans (Nat.mul_le_mul_right _ (by omega))

theorem exists_inv (ρ : Fin n → ℕ) (hinj : Function.Injective ρ) (L : List (Finset (Fin n)))
    (hdis : L.Pairwise Disjoint) (hs : ¬ Sorted ρ L) :
    ∃ A M C P Q i j, L = A ++ (P :: (M ++ (Q :: C))) ∧ i ∈ P ∧ j ∈ Q ∧ ρ j < ρ i := by
  unfold Sorted at hs
  rw [List.pairwise_iff_forall_sublist] at hs
  push_neg at hs
  obtain ⟨a, b, hsub, hab⟩ := hs
  obtain ⟨A, M, C, hL⟩ := sorted_decomp a b L hsub
  obtain ⟨i, hi, j, hj, hle⟩ := hab
  refine ⟨A, M, C, a, b, i, j, hL, hi, hj, ?_⟩
  subst hL
  obtain ⟨hPQ, _⟩ := disj_facts hdis
  have hne : i ≠ j := fun h => Finset.disjoint_left.mp hPQ hi (h ▸ hj)
  rcases lt_or_eq_of_le hle with h | h
  · exact h
  · exact absurd (hinj h) hne.symm

theorem phi_swap_lt (ρ : Fin n → ℕ) (A M C : List (Finset (Fin n))) (P Q : Finset (Fin n)) (i j : Fin n)
    (hi : i ∈ P) (hj : j ∈ Q) (hjP : j ∉ P) (hiQ : i ∉ Q) (hlt : ρ j < ρ i) :
    phi ρ (A ++ (P :: (M ++ (Q :: C)))) 1 <
      phi ρ (A ++ ((P.image (Equiv.swap i j)) :: (M ++ ((Q.image (Equiv.swap i j)) :: C)))) 1 := by
  rw [phi_mid, phi_mid]
  have e1 := wt_swap ρ P i j hi hjP
  have e2 := wt_swap ρ Q j i hj hiQ
  rw [Equiv.swap_comm] at e2
  have e1m := congrArg (fun x => (1 + A.length) * x) e1
  have e2m := congrArg (fun x => (1 + A.length + 1 + M.length) * x) e2
  have h3 : (1 + M.length) * ρ j < (1 + M.length) * ρ i := Nat.mul_lt_mul_of_pos_left hlt (by omega)
  beta_reduce at e1m e2m
  nlinarith

theorem sort_exists (B p0 : ℕ) (r d : Fin n → ℕ) (ρ : Fin n → ℕ) (hinj : Function.Injective ρ)
    (hρ : ∀ a b, ρ a < ρ b → r a ≤ r b ∧ d a ≤ d b) (L : List (Finset (Fin n)))
    (hL : Good B (equalTime p0) r d L) :
    ∃ L', Good B (equalTime p0) r d L' ∧ U L' = U L ∧ Sorted ρ L' := by
  have key : ∀ k, ∀ L : List (Finset (Fin n)), Good B (equalTime p0) r d L →
      (1 + n) * ∑ x ∈ U L, ρ x - phi ρ L 1 = k →
      ∃ L', Good B (equalTime p0) r d L' ∧ U L' = U L ∧ Sorted ρ L' := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro L hL hk
      by_cases hs : Sorted ρ L
      · exact ⟨L, hL, rfl, hs⟩
      · obtain ⟨A, M, C, P, Q, i, j, rfl, hi, hj, hlt⟩ := exists_inv ρ hinj L hL.2.1 hs
        obtain ⟨hL2, hU2⟩ := swap_good B p0 r d ρ hρ A M C P Q i j hL hi hj hlt
        obtain ⟨hPQ, _⟩ := disj_facts hL.2.1
        have hjP : j ∉ P := fun h => Finset.disjoint_left.mp hPQ h hj
        have hiQ : i ∉ Q := fun h => Finset.disjoint_left.mp hPQ hi h
        have hlt_phi := phi_swap_lt ρ A M C P Q i j hi hj hjP hiQ hlt
        have hb := phi_bound ρ _ (fun X hX => (hL2.1 X hX).1) hL2.2.1
        rw [hU2] at hb
        obtain ⟨L', h1, h2, h3⟩ := ih ((1 + n) * ∑ x ∈ U (A ++ (P :: (M ++ (Q :: C)))), ρ x -
          phi ρ (A ++ ((P.image (Equiv.swap i j)) :: (M ++ ((Q.image (Equiv.swap i j)) :: C)))) 1)
          (by omega) _ hL2 (by rw [hU2])
        exact ⟨L', h1, by rw [h2, hU2], h3⟩
  exact key _ L hL rfl

end SortMain

section Lemma4
variable {n : ℕ}

theorem optimal_struct (B : ℕ) (hB : 0 < B) (p r d : Fin n → ℕ) (L : List (Finset (Fin n)))
    (hL : Good B p r d L) (hmax : ∀ O', FS B p r d O' → O'.card ≤ (U L).card) :
    Optimal B p r d (L ++ singles (U L)) ∧
    ∀ P ∈ singles (U L), ∀ j ∈ P, d j < jobCompletion p r (L ++ singles (U L)) j := by
  have hS := valid_append_singles B hB p r d L hL
  have hmt := minTardy_eq B hB p r d (U L) ⟨L, hL, rfl⟩ hmax
  have hsub : U L ⊆ onTime p r d (L ++ singles (U L)) := by
    intro j hj
    simp only [onTime, Finset.mem_filter, Finset.mem_univ, true_and]
    exact completion_L B p r d L _ hL j hj
  have hc := tardyCount_eq p r d (L ++ singles (U L))
  have hge : minTardy B p r d ≤ tardyCount p r d (L ++ singles (U L)) := Nat.sInf_le ⟨_, hS, rfl⟩
  have hcard := Finset.card_le_card hsub
  have hUn : (U L).card ≤ n := by simpa using Finset.card_le_univ (U L)
  have htc : tardyCount p r d (L ++ singles (U L)) = minTardy B p r d := by omega
  refine ⟨⟨hS, htc⟩, ?_⟩
  have heq : U L = onTime p r d (L ++ singles (U L)) :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  intro P hP j hj
  obtain ⟨x, hx, rfl⟩ := mem_singles.mp hP
  rw [Finset.mem_singleton] at hj
  subst hj
  by_contra hcon
  have : j ∈ onTime p r d (L ++ singles (U L)) := by
    simp only [onTime, Finset.mem_filter, Finset.mem_univ, true_and]
    exact not_lt.mp hcon
  rw [← heq] at this
  exact hx this

theorem exists_rho (r d : Fin n → ℕ) (hag : ∀ i j : Fin n, r i < r j → d i ≤ d j) :
    ∃ ρ : Fin n → ℕ, Function.Injective ρ ∧ ∀ a b, ρ a < ρ b → r a ≤ r b ∧ d a ≤ d b := by
  let κ : Fin n → ℕ ×ₗ (ℕ ×ₗ Fin n) := fun a => toLex (r a, toLex (d a, a))
  have hκinj : Function.Injective κ := by
    intro a b h
    have := congrArg (fun x => (ofLex (ofLex x).2).2) h
    simpa [κ] using this
  let ρ : Fin n → ℕ := fun a => (Finset.univ.filter (fun c => κ c < κ a)).card
  have hlt : ∀ a b, κ a < κ b → ρ a < ρ b := by
    intro a b hab
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨a, by simpa using hab, by simp⟩
    · intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      exact hc.trans hab
  have hlt' : ∀ a b, ρ a < ρ b → κ a < κ b := by
    intro a b hab
    by_contra hcon
    rcases lt_or_eq_of_le (not_lt.mp hcon) with h | h
    · exact absurd (hlt _ _ h) (not_lt.mpr hab.le)
    · have := hκinj h
      subst this
      exact lt_irrefl _ hab
  refine ⟨ρ, ?_, ?_⟩
  · intro a b hab
    by_contra hne
    rcases lt_or_gt_of_ne (fun h => hne (hκinj h)) with h | h
    · exact absurd hab (ne_of_lt (hlt _ _ h))
    · exact absurd hab (ne_of_gt (hlt _ _ h))
  · intro a b hab
    have h := hlt' a b hab
    simp only [κ] at h
    rw [Prod.Lex.toLex_lt_toLex] at h
    simp only at h
    rcases h with h | ⟨h1, h2⟩
    · exact ⟨h.le, hag a b h⟩
    · rw [Prod.Lex.toLex_lt_toLex] at h2
      simp only at h2
      rcases h2 with h2 | ⟨h3, _⟩
      · exact ⟨h1.le, h2.le⟩
      · exact ⟨h1.le, h3.le⟩

theorem lemma4_core (B p : ℕ) (r d : Fin n → ℕ) (hB : 0 < B)
    (hagree : ∀ i j : Fin n, r i < r j → d i ≤ d j) :
    ∃ A T : List (Finset (Fin n)),
      Optimal B (equalTime p) r d (A ++ T) ∧
      (∀ P ∈ A, ∀ j ∈ P, jobCompletion (equalTime p) r (A ++ T) j ≤ d j) ∧
      (∀ P ∈ T, ∀ j ∈ P, d j < jobCompletion (equalTime p) r (A ++ T) j) ∧
      BatchEDD d A := by
  obtain ⟨ρ, hinj, hρ⟩ := exists_rho r d hagree
  obtain ⟨O, hO, hmax⟩ := exists_max_FS B (equalTime p) r d
  obtain ⟨L0, hL0, rfl⟩ := hO
  obtain ⟨L, hL, hUL, hsort⟩ := sort_exists B p r d ρ hinj hρ L0 hL0
  have hmax' : ∀ O', FS B (equalTime p) r d O' → O'.card ≤ (U L).card := by
    rw [hUL]; exact hmax
  obtain ⟨hopt, htard⟩ := optimal_struct B hB _ r d L hL hmax'
  refine ⟨L, singles (U L), hopt, ?_, htard, ?_⟩
  · intro P hP j hj
    exact completion_L B _ r d L _ hL j (mem_U.mpr ⟨P, hP, hj⟩)
  · intro a b hab i hi j hj
    have := List.pairwise_iff_getElem.mp hsort a b a.2 b.2 hab i hi j hj
    exact (hρ i j this).2

end Lemma4

end BurnInBatch.TardyJobs

open BurnInBatch.TardyJobs


theorem solution {n : ℕ} (B p : ℕ) (r d : Fin n → ℕ)
    (hB : 0 < B) (hagree : ∀ i j : Fin n, r i < r j → d i ≤ d j) :
    ∃ A T : List (Finset (Fin n)),
      Optimal B (equalTime p) r d (A ++ T) ∧
      (∀ P ∈ A, ∀ j ∈ P, jobCompletion (equalTime p) r (A ++ T) j ≤ d j) ∧
      (∀ P ∈ T, ∀ j ∈ P, d j < jobCompletion (equalTime p) r (A ++ T) j) ∧
      BatchEDD d A := by
  exact lemma4_core B p r d hB hagree
