-- Prove2me | solution 1 for DelayedSWPT.Extended.piE_feasible
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T04:46:57.475353+00:00
-- url     : https://prove2.me/submissions/1336ebe8-bb3c-4283-9496-fb9fc28ec447

import Mathlib
import Definitions.Def_DelayedSWPT_Extended_Problem



namespace DelayedSWPT.Extended

open DelayedSWPT.Model

section Gen
variable {n : ℕ} (r p : Fin n → ℕ) (prec : Fin n → Fin n → Prop) {inst : DecidableRel prec}

theorem dsw_foldl_spec (A : Finset (Fin n)) (l : List (Fin n)) (acc : Option (Fin n)) :
    (l.foldl (fun acc k =>
      if k ∈ A then
        (match acc with
         | none => some k
         | some b => if prec k b then some k else some b)
      else acc) acc = none → acc = none ∧ ∀ k ∈ l, k ∉ A) ∧
    (∀ j, l.foldl (fun acc k =>
      if k ∈ A then
        (match acc with
         | none => some k
         | some b => if prec k b then some k else some b)
      else acc) acc = some j → acc = some j ∨ j ∈ A) := by
  induction l generalizing acc with
  | nil => exact ⟨fun h => ⟨h, by simp⟩, fun j h => Or.inl h⟩
  | cons a l ih =>
    simp only [List.foldl_cons]
    obtain ⟨ih1, ih2⟩ := ih (if a ∈ A then
        (match acc with
         | none => some a
         | some b => if prec a b then some a else some b)
      else acc)
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := ih1 h
      by_cases ha : a ∈ A
      · rw [if_pos ha] at h1
        rcases acc with _ | b
        · simp at h1
        · simp only at h1; split_ifs at h1
      · rw [if_neg ha] at h1
        refine ⟨h1, ?_⟩
        intro k hk
        rcases List.mem_cons.1 hk with rfl | hk
        · exact ha
        · exact h2 k hk
    · intro j h
      rcases ih2 j h with h1 | h1
      · by_cases ha : a ∈ A
        · rw [if_pos ha] at h1
          rcases acc with _ | b
          · simp at h1; subst h1; exact Or.inr ha
          · simp only at h1
            split_ifs at h1
            · cases h1; exact Or.inr ha
            · exact Or.inl h1
        · rw [if_neg ha] at h1; exact Or.inl h1
      · exact Or.inr h1

theorem dsw_select_some (A : Finset (Fin n)) (j : Fin n) (h : select prec A = some j) : j ∈ A := by
  unfold select at h
  rcases (dsw_foldl_spec prec A _ none).2 j h with h | h
  · cases h
  · exact h

theorem dsw_select_none (A : Finset (Fin n)) (h : select prec A = none) : A = ∅ := by
  unfold select at h
  have := ((dsw_foldl_spec prec A _ none).1 h).2
  ext k; simp only [Finset.notMem_empty, iff_false]
  exact this k (List.mem_finRange k)

theorem dsw_choice_some (s : State n) (t : ℕ) (j : Fin n) (h : choice r prec s t = some j) :
    s.free ≤ t ∧ r j ≤ t ∧ s.start j = none := by
  unfold choice at h
  split_ifs at h with hf
  · have := dsw_select_some prec _ j h
    simp [available] at this
    exact ⟨hf, this⟩


theorem dsw_step_cases (s : State n) (t : ℕ) :
    (step r p prec t s = s ∧ ∀ j, choice r prec s t = some j → t < p j) ∨
    ∃ k, choice r prec s t = some k ∧ p k ≤ t ∧
      step r p prec t s = ⟨Function.update s.start k (some t), t + p k⟩ := by
  unfold step
  rcases hc : choice r prec s t with _ | k
  · left; simp
  · simp only
    by_cases hk : p k ≤ t
    · right; exact ⟨k, rfl, hk, by rw [if_pos hk]⟩
    · left; rw [if_neg hk]; refine ⟨rfl, ?_⟩
      intro j hj; cases hj; omega

local notation "SS" => stateAt r p prec

theorem dsw_stateAt_succ (t : ℕ) : SS (t+1) = step r p prec t (SS t) := rfl

theorem dsw_inv (t : ℕ) : ∀ j s, (SS t).start j = some s →
    s < t ∧ (SS s).start j = none ∧ choice r prec (SS s) s = some j ∧ p j ≤ s ∧
    s + p j ≤ (SS t).free ∧ (SS (s+1)).start j = some s := by
  induction t with
  | zero => intro j s h; simp [stateAt, initState] at h
  | succ t ih =>
    intro j s h
    rw [dsw_stateAt_succ] at h ⊢
    rcases dsw_step_cases r p prec (SS t) t with ⟨he, -⟩ | ⟨k, hc, hk, he⟩
    · rw [he] at h ⊢
      obtain ⟨a, b, c, d, e, f⟩ := ih j s h
      exact ⟨by omega, b, c, d, e, f⟩
    · rw [he] at h ⊢
      have hck := dsw_choice_some r prec _ _ _ hc
      by_cases hjk : j = k
      · subst hjk
        simp at h; subst h
        refine ⟨by omega, hck.2.2, hc, hk, le_refl _, ?_⟩
        rw [dsw_stateAt_succ, he]; simp
      · simp only [Function.update_of_ne hjk] at h
        obtain ⟨a, b, c, d, e, f⟩ := ih j s h
        exact ⟨by omega, b, c, d, by simp; omega, f⟩

theorem dsw_persist (t : ℕ) (j : Fin n) (s : ℕ) (h : (SS t).start j = some s) (m : ℕ) :
    (SS (t+m)).start j = some s := by
  induction m with
  | zero => simpa using h
  | succ m ih =>
    rw [← add_assoc, dsw_stateAt_succ]
    rcases dsw_step_cases r p prec (SS (t+m)) (t+m) with ⟨he, -⟩ | ⟨k, hc, hk, he⟩
    · rw [he]; exact ih
    · rw [he]
      have hck := dsw_choice_some r prec _ _ _ hc
      have hjk : j ≠ k := by rintro rfl; rw [ih] at hck; simp at hck
      simp only
      rw [Function.update_of_ne hjk]; exact ih

theorem dsw_persist' (t t' : ℕ) (j : Fin n) (s : ℕ) (h : (SS t).start j = some s) (ht : t ≤ t') :
    (SS t').start j = some s := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le ht
  exact dsw_persist r p prec t j s h m

theorem dsw_started_after (t t' : ℕ) (j : Fin n) (s : ℕ) (h : (SS t).start j = some s)
    (ht : s < t') : (SS t').start j = some s :=
  dsw_persist' r p prec (s+1) t' j s (dsw_inv r p prec t j s h).2.2.2.2.2 ht

theorem dsw_not_started_before (t t' : ℕ) (j : Fin n) (s : ℕ) (h : (SS t).start j = some s)
    (ht : t' ≤ s) : (SS t').start j = none := by
  rcases hh : (SS t').start j with _ | s'
  · rfl
  · exfalso
    have h1 := (dsw_inv r p prec t' j s' hh).1
    have h2 := dsw_started_after r p prec t' t j s' hh (by have := (dsw_inv r p prec t j s h).1; omega)
    rw [h] at h2; cases h2; omega

theorem dsw_nonoverlap (t : ℕ) (i j : Fin n) (si sj : ℕ) (hi : (SS t).start i = some si)
    (hj : (SS t).start j = some sj) (hij : i ≠ j) : si + p i ≤ sj ∨ sj + p j ≤ si := by
  have Ii := dsw_inv r p prec t i si hi
  have Ij := dsw_inv r p prec t j sj hj
  rcases lt_trichotomy si sj with h | h | h
  · left
    have h1 := dsw_started_after r p prec t sj i si hi h
    have h2 := (dsw_inv r p prec sj i si h1)
    have h3 := dsw_choice_some r prec _ _ _ Ij.2.2.1
    omega
  · subst h
    exfalso; apply hij
    have := Ii.2.2.1; rw [Ij.2.2.1] at this; cases this; rfl
  · right
    have h1 := dsw_started_after r p prec t si j sj hj h
    have h2 := (dsw_inv r p prec si j sj h1)
    have h3 := dsw_choice_some r prec _ _ _ Ii.2.2.1
    omega

theorem dsw_free_bound (t : ℕ) :
    (SS t).free ≤ t + ∑ i ∈ Finset.univ.filter (fun i => (SS t).start i ≠ none), p i := by
  induction t with
  | zero => simp [stateAt, initState]
  | succ t ih =>
    rw [dsw_stateAt_succ]
    rcases dsw_step_cases r p prec (SS t) t with ⟨he, -⟩ | ⟨k, hc, hk, he⟩
    · rw [he]; omega
    · rw [he]
      simp only
      have : p k ≤ ∑ i ∈ Finset.univ.filter
          (fun i => Function.update (SS t).start k (some t) i ≠ none), p i := by
        apply Finset.single_le_sum (f := p) (fun _ _ => Nat.zero_le _)
        simp
      omega


theorem dsw_U_step (s : Fin n → Option ℕ) (k : Fin n) (t : ℕ) (hk : s k = none) :
    ∑ i ∈ Finset.univ.filter (fun i => Function.update s k (some t) i = none), p i + p k =
    ∑ i ∈ Finset.univ.filter (fun i => s i = none), p i := by
  have : Finset.univ.filter (fun i => Function.update s k (some t) i = none) =
      (Finset.univ.filter (fun i => s i = none)).erase k := by
    ext i
    by_cases hi : i = k
    · subst hi; simp
    · simp [hi]
  rw [this, add_comm]
  exact Finset.add_sum_erase _ _ (by simp [hk])

theorem dsw_all_started (hp : ∀ k, 1 ≤ p k) (j : Fin n) : (SS (horizon r p)).start j ≠ none := by
  intro hj
  set P := ∑ i, p i with hP
  set H := horizon r p with hH
  have hrj : r j ≤ ∑ i, r i := Finset.single_le_sum (f := r) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have hpk : ∀ k, p k ≤ P := fun k => Finset.single_le_sum (f := p) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  have hHv : H = ∑ i, r i + 2 * P + 1 := by
    rw [hH, horizon, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hsplit : ∀ t, ∑ i ∈ Finset.univ.filter (fun i => (SS t).start i ≠ none), p i +
      ∑ i ∈ Finset.univ.filter (fun i => (SS t).start i = none), p i = P := by
    intro t
    rw [add_comm]
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  have claim : ∀ m, r j + P + m ≤ H →
      max (SS (r j + P + m)).free (r j + P + m) +
        ∑ i ∈ Finset.univ.filter (fun i => (SS (r j + P + m)).start i = none), p i ≤ r j + P + P := by
    intro m
    induction m with
    | zero =>
      intro _
      have h1 := dsw_free_bound r p prec (inst := inst) (r j + P)
      have h2 := hsplit (r j + P)
      simp only [add_zero]
      omega
    | succ m ih =>
      intro hm
      have ih := ih (by omega)
      have hju : (SS (r j + P + m)).start j = none := by
        rcases hh : (SS (r j + P + m)).start j with _ | s
        · rfl
        · exfalso; have := dsw_persist' r p prec _ H j s hh (by omega); rw [hj] at this; cases this
      rw [← add_assoc, dsw_stateAt_succ]
      rcases dsw_step_cases r p prec (SS (r j + P + m)) (r j + P + m) with ⟨he, hn⟩ | ⟨k, hc, hk, he⟩
      · rw [he]
        by_cases hf : (SS (r j + P + m)).free ≤ r j + P + m
        · exfalso
          rcases hs : select prec (available r (SS (r j + P + m)) (r j + P + m)) with _ | k
          · have := dsw_select_none prec _ hs
            have hmem : j ∈ available r (SS (r j + P + m)) (r j + P + m) := by
              simp [available, hju]; omega
            rw [this] at hmem; simp at hmem
          · have := hn k (by unfold choice; rw [if_pos hf]; exact hs)
            have := hpk k; omega
        · omega
      · rw [he]
        have hck := dsw_choice_some r prec _ _ _ hc
        have := dsw_U_step p (SS (r j + P + m)).start k (r j + P + m) hck.2.2
        simp only
        have := hpk k
        have := hp k
        omega
  have := claim (H - (r j + P)) (by omega)
  rw [show r j + P + (H - (r j + P)) = H by omega] at this
  omega

end Gen

section Spec
variable {n : ℕ} (I : Instance n)

theorem dsw_inv' (t : ℕ) (j : Fin n) (s : ℕ) (h : (dswptState I t).start j = some s) :
    s < t ∧ (dswptState I s).start j = none ∧ dswptChoice I s = some j ∧ I.p j ≤ s ∧
    s + I.p j ≤ (dswptState I t).free ∧ (dswptState I (s+1)).start j = some s :=
  dsw_inv I.r I.p (Prec I) (inst := Classical.decRel _) t j s h

theorem dsw_choice_some' (t : ℕ) (j : Fin n) (h : dswptChoice I t = some j) :
    (dswptState I t).free ≤ t ∧ I.r j ≤ t ∧ (dswptState I t).start j = none :=
  dsw_choice_some I.r (Prec I) (inst := Classical.decRel _) _ t j h

theorem dsw_final (j : Fin n) : (dswptState I (horizon I.r I.p)).start j = some (dswpt I j) := by
  have := dsw_all_started I.r I.p (Prec I) (inst := Classical.decRel _) I.p_pos j
  unfold dswpt
  change (dswptState I (horizon I.r I.p)).start j ≠ none at this
  rcases h : (dswptState I (horizon I.r I.p)).start j with _ | s
  · exact absurd h this
  · rfl

theorem dsw_p_le (j : Fin n) : I.p j ≤ dswpt I j ∧ I.r j ≤ dswpt I j := by
  have h := dsw_inv' I _ j _ (dsw_final I j)
  exact ⟨h.2.2.2.1, (dsw_choice_some' I _ j h.2.2.1).2.1⟩

theorem dsw_nonoverlap' (i j : Fin n) (hij : i ≠ j) :
    dswpt I i + I.p i ≤ dswpt I j ∨ dswpt I j + I.p j ≤ dswpt I i :=
  dsw_nonoverlap I.r I.p (Prec I) (inst := Classical.decRel _) _ i j _ _
    (dsw_final I i) (dsw_final I j) hij

theorem dsw_started_at (t : ℕ) (k : Fin n) (h : dswpt I k < t) :
    (dswptState I t).start k = some (dswpt I k) :=
  dsw_started_after I.r I.p (Prec I) (inst := Classical.decRel _) _ t k _ (dsw_final I k) h

theorem f_le_two (t : ℕ) : f I t ≤ 2 * t := by
  unfold f
  split_ifs with h
  · have h1 := h.choose_spec
    have h2 := (dsw_p_le I h.choose).1
    omega
  · omega

theorem rPrime_le_core (j : Fin n) : rPrime I j ≤ max (2 * I.r j) (I.p j) := by
  unfold rPrime
  have := f_le_two I (I.r j)
  exact max_le (le_max_right _ _) (le_trans this (le_max_left _ _))

theorem gap_spec (g : gapTimes I) : dswptChoice I g.1 = some (gapJob I g) ∧ g.1 < I.p (gapJob I g) := by
  classical
  obtain ⟨j, hj, hjt⟩ := (Finset.mem_filter.1 g.2).2
  have : dswptChoice I g.1 = some (gapJob I g) := by unfold gapJob; simp
  rw [hj] at this; cases this
  exact ⟨hj, hjt⟩

theorem piE_feasible_core : IsFeasible (rE I) (pE I) (piE I) := by
  refine ⟨?_, ?_⟩
  · rintro (j | g)
    · simp only [rE, piE, Sum.elim_inl]
      unfold rPrime
      refine max_le (dsw_p_le I j).1 ?_
      unfold f
      split_ifs with h
      · have h1 := h.choose_spec
        have hne : h.choose ≠ j := by
          intro e; have := (dsw_p_le I j).2; rw [e] at h1; omega
        rcases dsw_nonoverlap' I _ _ hne with h2 | h2
        · exact h2
        · have := (dsw_p_le I j).2; omega
      · exact (dsw_p_le I j).2
    · simp only [rE, piE, Sum.elim_inr]
      obtain ⟨hc, -⟩ := gap_spec I g
      have hcs := dsw_choice_some' I _ _ hc
      unfold f
      split_ifs with h
      · have h1 := h.choose_spec
        have hst := dsw_started_at I g.1 h.choose (by omega)
        have := (dsw_inv' I _ _ _ hst).2.2.2.2.1
        omega
      · exact hcs.2.1
  · have key : ∀ (j : Fin n) (g : gapTimes I),
        dswpt I j + I.p j ≤ g.1 ∨ g.1 + 1 ≤ dswpt I j := by
      intro j g
      by_contra hcon
      push_neg at hcon
      obtain ⟨hc, hgt⟩ := gap_spec I g
      have hcs := dsw_choice_some' I _ _ hc
      rcases Nat.lt_or_ge (dswpt I j) g.1 with hlt | hge
      · have hst := dsw_started_at I g.1 j hlt
        have := (dsw_inv' I _ _ _ hst).2.2.2.2.1
        omega
      · have he : dswpt I j = g.1 := by omega
        have hI := dsw_inv' I _ j _ (dsw_final I j)
        rw [he, hc] at hI
        obtain ⟨-, -, h3, h4, -⟩ := hI
        cases h3; omega
    rintro (i | g) (j | g') hij
    · simp only [pE, piE, Sum.elim_inl]
      exact dsw_nonoverlap' I i j (fun e => hij (by rw [e]))
    · simp only [pE, piE, Sum.elim_inl, Sum.elim_inr]
      exact key i g'
    · simp only [pE, piE, Sum.elim_inl, Sum.elim_inr]
      exact (key j g).symm
    · simp only [pE, piE, Sum.elim_inr]
      have : g.1 ≠ g'.1 := fun e => hij (by rw [Subtype.ext e])
      omega

end Spec
end DelayedSWPT.Extended

open DelayedSWPT.Extended
open DelayedSWPT.Model

theorem solution {n : ℕ} (I : Instance n) : IsFeasible (rE I) (pE I) (piE I) := by
  exact piE_feasible_core I
