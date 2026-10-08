-- Prove2me | solution 1 for DelayedSWPT.Extended.piE_optimal
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T04:55:00.513909+00:00
-- url     : https://prove2.me/submissions/6bee2b43-f551-4a68-89a3-5ca491008bcb

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
section Greedy
variable {U : Type*} [Fintype U] [DecidableEq U] (ρ A B : U → ℕ)

theorem ug_count (hB : Function.Injective B) (hBr : ∀ u, ρ u ≤ B u)
    (H : Finset U) (hH : ∀ v ∈ H, ∀ τ, ρ v ≤ τ → τ < A v → ∃ u ∈ H, A u = τ) (T : ℕ) :
    (H.filter (fun u => B u < T)).card ≤ (H.filter (fun u => A u < T)).card := by
  induction T with
  | zero => simp
  | succ T ih =>
    by_cases hT : ∃ u ∈ H, A u = T
    · obtain ⟨u0, hu0, hA0⟩ := hT
      have eA : H.filter (fun u => A u < T + 1) =
          H.filter (fun u => A u < T) ∪ H.filter (fun u => A u = T) := by
        ext u; by_cases hu : u ∈ H <;> simp [hu]; omega
      have dA : Disjoint (H.filter (fun u => A u < T)) (H.filter (fun u => A u = T)) := by
        rw [Finset.disjoint_filter]; intro u _ h1 h2; omega
      have sB : H.filter (fun u => B u < T + 1) ⊆
          H.filter (fun u => B u < T) ∪ H.filter (fun u => B u = T) := by
        intro u; by_cases hu : u ∈ H <;> simp [hu]; omega
      have c1 : (H.filter (fun u => B u = T)).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro a ha b hb
        simp only [Finset.mem_filter] at ha hb
        exact hB (ha.2.trans hb.2.symm)
      have c2 : 1 ≤ (H.filter (fun u => A u = T)).card :=
        Finset.card_pos.2 ⟨u0, by simp [hu0, hA0]⟩
      have := Finset.card_le_card sB
      have := Finset.card_union_le (H.filter (fun u => B u < T)) (H.filter (fun u => B u = T))
      rw [eA, Finset.card_union_of_disjoint dA]
      omega
    · push_neg at hT
      apply Finset.card_le_card
      intro u
      simp only [Finset.mem_filter]
      rintro ⟨hu, hb⟩
      refine ⟨hu, ?_⟩
      by_contra hc
      obtain ⟨u', hu', he⟩ := hH u hu T (by have := hBr u; omega) (by omega)
      exact hT u' hu' he

theorem ug_sum_eq (X : U → ℕ) (H : Finset U) (N : ℕ) (hN : ∀ u ∈ H, X u ≤ N) :
    ∑ u ∈ H, X u = ∑ T ∈ Finset.range N, (H.filter (fun u => T < X u)).card := by
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  rw [← Finset.card_filter]
  have : (Finset.range N).filter (fun T => T < X u) = Finset.range (X u) := by
    ext T; simp only [Finset.mem_filter, Finset.mem_range]; have := hN u hu; omega
  rw [this, Finset.card_range]

theorem ug_sum (hB : Function.Injective B) (hBr : ∀ u, ρ u ≤ B u)
    (H : Finset U) (hH : ∀ v ∈ H, ∀ τ, ρ v ≤ τ → τ < A v → ∃ u ∈ H, A u = τ) :
    ∑ u ∈ H, A u ≤ ∑ u ∈ H, B u := by
  set N := ∑ u ∈ H, (A u + B u)
  have hNA : ∀ u ∈ H, A u ≤ N := fun u hu =>
    le_trans (by omega) (Finset.single_le_sum (f := fun u => A u + B u) (fun _ _ => Nat.zero_le _) hu)
  have hNB : ∀ u ∈ H, B u ≤ N := fun u hu =>
    le_trans (by omega) (Finset.single_le_sum (f := fun u => A u + B u) (fun _ _ => Nat.zero_le _) hu)
  rw [ug_sum_eq A H N hNA, ug_sum_eq B H N hNB]
  apply Finset.sum_le_sum
  intro T _
  have h1 := ug_count ρ A B hB hBr H hH (T+1)
  have e1 := Finset.card_filter_add_card_filter_not (s := H) (fun u => A u < T + 1)
  have e2 := Finset.card_filter_add_card_filter_not (s := H) (fun u => B u < T + 1)
  have f1 : H.filter (fun u => ¬ A u < T + 1) = H.filter (fun u => T < A u) := by
    ext u; by_cases hu : u ∈ H <;> simp [hu]
  have f2 : H.filter (fun u => ¬ B u < T + 1) = H.filter (fun u => T < B u) := by
    ext u; by_cases hu : u ∈ H <;> simp [hu]
  rw [f1] at e1; rw [f2] at e2
  omega

theorem ug_weighted (ω : U → ℝ) (hB : Function.Injective B) (hBr : ∀ u, ρ u ≤ B u)
    (hgreedy : ∀ u v, ρ v ≤ A u → A u < A v → ω v ≤ ω u)
    (hidle : ∀ v τ, ρ v ≤ τ → τ < A v → ∃ u, A u = τ) :
    ∀ k, ∀ H : Finset U, H.card ≤ k → (∀ u ∈ H, ∀ v, ω u ≤ ω v → v ∈ H) →
      ∀ c : ℝ, (∀ u ∈ H, c ≤ ω u) →
      ∑ u ∈ H, (ω u - c) * (A u : ℝ) ≤ ∑ u ∈ H, (ω u - c) * (B u : ℝ) := by
  intro k
  induction k with
  | zero =>
    intro H hH _ c _
    have : H = ∅ := Finset.card_eq_zero.1 (by omega)
    subst this; simp
  | succ k ih =>
    intro H hH hup c hc
    rcases H.eq_empty_or_nonempty with rfl | hne
    · simp
    obtain ⟨m, hm, hmin⟩ := H.exists_min_image ω hne
    set H' := H.filter (fun u => ω m < ω u)
    have hH'card : H'.card ≤ k := by
      have : H' ⊂ H := by
        refine Finset.ssubset_iff_subset_ne.2 ⟨Finset.filter_subset _ _, ?_⟩
        intro e
        have : m ∈ H' := by rw [e]; exact hm
        simp [H'] at this
      have := Finset.card_lt_card this; omega
    have hup' : ∀ u ∈ H', ∀ v, ω u ≤ ω v → v ∈ H' := by
      intro u hu v huv
      simp only [H', Finset.mem_filter] at hu ⊢
      exact ⟨hup u hu.1 v huv, lt_of_lt_of_le hu.2 huv⟩
    have ih' := ih H' hH'card hup' (ω m) (fun u hu => by simp [H'] at hu; exact hu.2.le)
    have hHclosed : ∀ v ∈ H, ∀ τ, ρ v ≤ τ → τ < A v → ∃ u ∈ H, A u = τ := by
      intro v hv τ h1 h2
      obtain ⟨u, hu⟩ := hidle v τ h1 h2
      refine ⟨u, hup v hv u ?_, hu⟩
      exact hgreedy u v (by omega) (by omega)
    have hs := ug_sum ρ A B hB hBr H hHclosed
    have hsR : (∑ u ∈ H, (A u : ℝ)) ≤ ∑ u ∈ H, (B u : ℝ) := by exact_mod_cast hs
    have split : ∀ X : U → ℕ, ∑ u ∈ H, (ω u - c) * (X u : ℝ) =
        (ω m - c) * ∑ u ∈ H, (X u : ℝ) + ∑ u ∈ H', (ω u - ω m) * (X u : ℝ) := by
      intro X
      rw [Finset.mul_sum, Finset.sum_filter, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro u hu
      split_ifs with h
      · ring
      · have : ω u = ω m := le_antisymm (not_lt.1 h) (hmin u hu)
        rw [this]; ring
    rw [split A, split B]
    have hcm : 0 ≤ ω m - c := by have := hc m hm; linarith
    have := mul_le_mul_of_nonneg_left hsR hcm
    linarith

theorem unit_greedy (ω : U → ℝ) (hω : ∀ u, 0 ≤ ω u)
    (hB : Function.Injective B) (hBr : ∀ u, ρ u ≤ B u)
    (hgreedy : ∀ u v, ρ v ≤ A u → A u < A v → ω v ≤ ω u)
    (hidle : ∀ v τ, ρ v ≤ τ → τ < A v → ∃ u, A u = τ) :
    ∑ u, ω u * (A u : ℝ) ≤ ∑ u, ω u * (B u : ℝ) := by
  have := ug_weighted ρ A B ω hB hBr hgreedy hidle _ Finset.univ le_rfl (by simp) 0
    (fun u _ => hω u)
  simpa using this

end Greedy

section Opt
variable {n : ℕ} (I : Instance n)

/-- `j` is at least as good as `k` in the ratio order. -/
def Dom (j k : Fin n) : Prop := (I.p j : ℝ) * I.w k ≤ (I.p k : ℝ) * I.w j

theorem dom_trans (a b c : Fin n) (h1 : Dom I a b) (h2 : Dom I b c) : Dom I a c := by
  unfold Dom at *
  have hb : (0 : ℝ) < I.p b := by have := I.p_pos b; exact_mod_cast (by omega : 0 < I.p b)
  have hwb := I.w_pos b
  have hpa : (0 : ℝ) ≤ I.p a := Nat.cast_nonneg _
  have hpc : (0 : ℝ) ≤ I.p c := Nat.cast_nonneg _
  have hwa := I.w_pos a
  have hwc := I.w_pos c
  have := mul_le_mul h1 h2 (by positivity) (by positivity)
  have h3 : ((I.p b : ℝ) * I.w b) * ((I.p a) * I.w c) ≤ ((I.p b : ℝ) * I.w b) * (I.p c * I.w a) := by
    nlinarith
  exact le_of_mul_le_mul_left h3 (by positivity)

theorem dom_select_aux (A : Finset (Fin n)) {inst : DecidableRel (Prec I)} (l : List (Fin n))
    (acc : Option (Fin n)) (j : Fin n) :
    l.foldl (fun acc k =>
      if k ∈ A then
        (match acc with
         | none => some k
         | some b => if Prec I k b then some k else some b)
      else acc) acc = some j →
    (∀ k ∈ l, k ∈ A → Dom I j k) ∧ (∀ b, acc = some b → Dom I j b) := by
  induction l generalizing acc with
  | nil =>
    intro h; simp at h; subst h
    exact ⟨by simp, fun b hb => by cases hb; unfold Dom; exact le_refl _⟩
  | cons a l ih =>
    intro h
    simp only [List.foldl_cons] at h
    obtain ⟨h1, h2⟩ := ih _ h
    refine ⟨?_, ?_⟩
    · intro k hk hkA
      rcases List.mem_cons.1 hk with rfl | hk
      · rw [if_pos hkA] at h2
        rcases acc with _ | b
        · exact h2 k rfl
        · simp only at h2
          split_ifs at h2 with hp
          · exact h2 k rfl
          · apply dom_trans I _ b _ (h2 b rfl)
            unfold Dom; unfold Prec at hp; push_neg at hp; exact hp.1
      · exact h1 k hk hkA
    · intro b hb
      subst hb
      by_cases haA : a ∈ A
      · rw [if_pos haA] at h2
        simp only at h2
        split_ifs at h2 with hp
        · apply dom_trans I _ a _ (h2 a rfl)
          unfold Dom; unfold Prec at hp
          rcases hp with hp | hp
          · exact hp.le
          · exact hp.1.le
        · exact h2 b rfl
      · rw [if_neg haA] at h2; exact h2 b rfl

theorem dom_choice (t : ℕ) (c k : Fin n) (hc : dswptChoice I t = some c)
    (hk : I.r k ≤ t) (hk2 : (dswptState I t).start k = none) : Dom I c k := by
  unfold dswptChoice choice at hc
  split_ifs at hc
  unfold select at hc
  exact (dom_select_aux I _ _ none c hc).1 k (List.mem_finRange k) (by simp [available, hk, hk2])

theorem dsw_free_inv (t : ℕ) : (dswptState I t).free ≤ t ∨
    ∃ k s, (dswptState I t).start k = some s ∧ s + I.p k = (dswptState I t).free := by
  induction t with
  | zero => left; simp [dswptState, stateAt, initState]
  | succ t ih =>
    have e : dswptState I (t+1) = @step n I.r I.p (Prec I) (Classical.decRel _) t (dswptState I t) := rfl
    rw [e]
    rcases dsw_step_cases I.r I.p (Prec I) (inst := Classical.decRel _) (dswptState I t) t with
      ⟨he, -⟩ | ⟨k, hc, hk, he⟩
    · rw [he]
      rcases ih with h | ⟨k, s, h1, h2⟩
      · left; omega
      · right; exact ⟨k, s, h1, h2⟩
    · rw [he]; right; exact ⟨k, t, by simp, rfl⟩

theorem dsw_unstarted_le (t : ℕ) (k : Fin n) (h : (dswptState I t).start k = none) :
    t ≤ dswpt I k := by
  by_contra hc
  have := dsw_started_at I t k (by omega)
  rw [h] at this; cases this

theorem dsw_lt_horizon (k : Fin n) : dswpt I k < horizon I.r I.p :=
  (dsw_inv' I _ k _ (dsw_final I k)).1

theorem f_ge (t : ℕ) : t ≤ f I t := by
  unfold f; split_ifs with h
  · have := h.choose_spec; omega
  · exact le_refl _

theorem f_eq (x : ℕ) (k : Fin n) (h1 : dswpt I k < x) (h2 : x < dswpt I k + I.p k) :
    f I x = dswpt I k + I.p k := by
  unfold f
  have hex : ∃ j, dswpt I j < x ∧ x < dswpt I j + I.p j := ⟨k, h1, h2⟩
  rw [dif_pos hex]
  have hs := hex.choose_spec
  by_cases e : hex.choose = k
  · rw [e]
  · rcases dsw_nonoverlap' I _ _ e with h | h <;> omega

end Opt

section Opt2
variable {n : ℕ} (I : Instance n)

abbrev UnitE := Σ e : EJob I, Fin (pE I e)

theorem pE_pos (e : EJob I) : 1 ≤ pE I e := by
  rcases e with j | g
  · exact I.p_pos j
  · simp [pE]

theorem sum_range_lin (S p : ℕ) : ∑ i ∈ Finset.range p, ((S + i : ℕ) : ℝ) =
    (p : ℝ) * S + (p : ℝ) * ((p : ℝ) - 1) / 2 := by
  induction p with
  | zero => simp
  | succ p ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem cost_units (S : EJob I → ℕ) : cost (wE I) (pE I) S =
    ∑ u : UnitE I, (wE I u.1 / pE I u.1) * ((S u.1 + u.2 : ℕ) : ℝ) +
      ∑ e, wE I e * (((pE I e : ℝ) + 1) / 2) := by
  unfold cost
  rw [Fintype.sum_sigma, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  have h := Fin.sum_univ_eq_sum_range (fun i => (wE I e / pE I e) * ((S e + i : ℕ) : ℝ)) (pE I e)
  rw [h, ← Finset.mul_sum, sum_range_lin]
  have hp : (0 : ℝ) < pE I e := by have := pE_pos I e; exact_mod_cast (by omega : 0 < pE I e)
  push_cast
  field_simp
  ring

theorem gap_key (j : Fin n) (g : gapTimes I) :
    dswpt I j + I.p j ≤ g.1 ∨ g.1 + 1 ≤ dswpt I j := by
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

theorem unitA_info (u : UnitE I) : ∃ s c, dswptChoice I s = some c ∧ s ≤ piE I u.1 + u.2 ∧
    wE I u.1 / pE I u.1 = I.w c / I.p c ∧
    (∀ x, s < x → x ≤ piE I u.1 + u.2 → piE I u.1 + u.2 < f I x) ∧
    (∀ k, dswpt I k ≤ piE I u.1 + u.2 → piE I u.1 + u.2 < dswpt I k + I.p k → u.1 = Sum.inl k) := by
  obtain ⟨e, i⟩ := u
  rcases e with j | g
  · have hi : (i : ℕ) < I.p j := i.isLt
    simp only [piE, wE, pE, Sum.elim_inl]
    refine ⟨dswpt I j, j, (dsw_inv' I _ j _ (dsw_final I j)).2.2.1, by omega, rfl, ?_, ?_⟩
    · intro x h1 h2
      rw [f_eq I x j h1 (by omega)]; omega
    · intro k h1 h2
      by_contra hne
      have hne' : j ≠ k := fun e => hne (by rw [e])
      rcases dsw_nonoverlap' I _ _ hne' with h | h <;> omega
  · have hi : (i : ℕ) < 1 := i.isLt
    simp only [piE, wE, pE, Sum.elim_inr]
    obtain ⟨hc, -⟩ := gap_spec I g
    refine ⟨g.1, gapJob I g, hc, by omega, by simp [gapWeight], ?_, ?_⟩
    · intro x h1 h2; omega
    · intro k h1 h2
      rcases gap_key I k g with h | h <;> omega

theorem unitV_info (v : UnitE I) : ∃ k, wE I v.1 / pE I v.1 = I.w k / I.p k ∧
    f I (I.r k) ≤ rE I v.1 ∧
    ∀ τ, τ < piE I v.1 + v.2 →
      (dswpt I k ≤ τ ∧ τ < dswpt I k + I.p k ∧ v.1 = Sum.inl k) ∨ τ < dswpt I k := by
  obtain ⟨e, i⟩ := v
  rcases e with k | g
  · have hi : (i : ℕ) < I.p k := i.isLt
    simp only [piE, wE, pE, rE, Sum.elim_inl]
    refine ⟨k, rfl, by unfold rPrime; exact le_max_right _ _, ?_⟩
    intro τ hτ
    by_cases h : dswpt I k ≤ τ
    · left; exact ⟨h, by omega, rfl⟩
    · right; omega
  · have hi : (i : ℕ) < 1 := i.isLt
    simp only [piE, wE, pE, rE, Sum.elim_inr]
    obtain ⟨hc, -⟩ := gap_spec I g
    have hcs := dsw_choice_some' I _ _ hc
    have := dsw_unstarted_le I _ _ hcs.2.2
    refine ⟨gapJob I g, by simp [gapWeight], le_refl _, ?_⟩
    intro τ hτ; right; omega

theorem dom_div (c k : Fin n) (h : Dom I c k) : I.w k / I.p k ≤ I.w c / I.p c := by
  have hk : (0 : ℝ) < I.p k := by have := I.p_pos k; exact_mod_cast (by omega : 0 < I.p k)
  have hc : (0 : ℝ) < I.p c := by have := I.p_pos c; exact_mod_cast (by omega : 0 < I.p c)
  rw [div_le_div_iff₀ hk hc]
  unfold Dom at h; linarith

theorem piE_greedy (u v : UnitE I) (hρ : rE I v.1 ≤ piE I u.1 + u.2)
    (hlt : piE I u.1 + u.2 < piE I v.1 + v.2) :
    wE I v.1 / pE I v.1 ≤ wE I u.1 / pE I u.1 := by
  obtain ⟨s, c, hc, hs, hwu, hP, hcov⟩ := unitA_info I u
  obtain ⟨k, hwv, hfk, hτ⟩ := unitV_info I v
  rcases hτ _ hlt with ⟨h1, h2, h3⟩ | h
  · have := hcov k h1 h2
    rw [h3, ← this]
  · rw [hwu, hwv]
    apply dom_div
    have hns := dsw_not_started_before I.r I.p (Prec I) (inst := Classical.decRel _) _ s k _
      (dsw_final I k) (by omega)
    have hrk : I.r k ≤ s := by
      by_contra hcon
      have := hP (I.r k) (by omega) (by have := f_ge I (I.r k); omega)
      omega
    exact dom_choice I s c k hc hrk hns

end Opt2

section Opt3
variable {n : ℕ} (I : Instance n)

theorem piE_idle (v : UnitE I) (τ : ℕ) (hρ : rE I v.1 ≤ τ) (hτ : τ < piE I v.1 + v.2) :
    ∃ u : UnitE I, piE I u.1 + u.2 = τ := by
  by_cases hcov : ∃ j, dswpt I j ≤ τ ∧ τ < dswpt I j + I.p j
  · obtain ⟨j, h1, h2⟩ := hcov
    exact ⟨⟨Sum.inl j, ⟨τ - dswpt I j, by simp [pE]; omega⟩⟩, by simp [piE]; omega⟩
  push_neg at hcov
  obtain ⟨k, -, hfk, hτk⟩ := unitV_info I v
  rcases hτk τ hτ with ⟨h1, h2, -⟩ | hk
  · exact absurd h2 (not_lt.2 (hcov k h1))
  have hH := dsw_lt_horizon I k
  have hns := dsw_not_started_before I.r I.p (Prec I) (inst := Classical.decRel _) _ τ k _
    (dsw_final I k) (by omega)
  change (dswptState I τ).start k = none at hns
  have hrk : I.r k ≤ τ := by have := f_ge I (I.r k); omega
  have hfree : (dswptState I τ).free ≤ τ := by
    by_contra hlt
    rcases dsw_free_inv I τ with h | ⟨k', s', h1, h2⟩
    · exact hlt h
    · 
      have hs' := (dsw_inv' I _ _ _ h1).1
      have hfin := dsw_persist' I.r I.p (Prec I) (inst := Classical.decRel _) τ (horizon I.r I.p)
        k' s' h1 (by omega)
      have : dswpt I k' = s' := by
        have := dsw_final I k'
        change (dswptState I (horizon I.r I.p)).start k' = some s' at hfin
        rw [hfin] at this; cases this; rfl
      have := hcov k' (by omega)
      omega
  obtain ⟨c, hc⟩ : ∃ c, dswptChoice I τ = some c := by
    unfold dswptChoice choice
    rw [if_pos hfree]
    rcases hs : @select n (Prec I) (Classical.decRel _) (available I.r (dswptState I τ) τ) with _ | c
    · have := dsw_select_none (Prec I) (inst := Classical.decRel _) _ hs
      have hmem : k ∈ available I.r (dswptState I τ) τ := by simp [available, hns, hrk]
      rw [this] at hmem; simp at hmem
    · exact ⟨c, rfl⟩
  rcases dsw_step_cases I.r I.p (Prec I) (inst := Classical.decRel _) (dswptState I τ) τ with
    ⟨he, hn⟩ | ⟨k'', hc'', hk'', he⟩
  · have hgt := hn c hc
    have hmem : τ ∈ gapTimes I := by
      classical
      unfold gapTimes
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, c, hc, hgt⟩
    exact ⟨⟨Sum.inr ⟨τ, hmem⟩, ⟨0, by simp [pE]⟩⟩, by simp [piE]⟩
  · exfalso
    have h1 : (dswptState I (τ+1)).start k'' = some τ := by
      have e : dswptState I (τ+1) = @step n I.r I.p (Prec I) (Classical.decRel _) τ (dswptState I τ) := rfl
      rw [e, he]; simp
    have hfin := dsw_persist' I.r I.p (Prec I) (inst := Classical.decRel _) (τ+1) (horizon I.r I.p)
        k'' τ h1 (by omega)
    have : dswpt I k'' = τ := by
      have := dsw_final I k''
      change (dswptState I (horizon I.r I.p)).start k'' = some τ at hfin
      rw [hfin] at this; cases this; rfl
    have := hcov k'' (by omega)
    have := I.p_pos k''
    omega

theorem piE_optimal_core : IsOptimal (rE I) (pE I) (wE I) (piE I) := by
  classical
  refine ⟨piE_feasible_core I, fun S' hS' => ?_⟩
  rw [cost_units I, cost_units I]
  refine add_le_add ?_ le_rfl
  refine unit_greedy (fun u : UnitE I => rE I u.1) (fun u => piE I u.1 + u.2)
    (fun u => S' u.1 + u.2) (fun u => wE I u.1 / pE I u.1) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨e, i⟩
    rcases e with j | g
    · simp only [wE, pE, Sum.elim_inl]; have := I.w_pos j; positivity
    · simp only [wE, pE, Sum.elim_inr, gapWeight]; have := I.w_pos (gapJob I g); positivity
  · rintro ⟨e, i⟩ ⟨e', i'⟩ h
    simp only at h
    by_cases he : e = e'
    · subst he
      have : i = i' := Fin.ext (by omega)
      subst this; rfl
    · have := hS'.2 e e' he
      have := i.isLt; have := i'.isLt
      omega
  · rintro ⟨e, i⟩
    have := hS'.1 e
    simp only; omega
  · intro u v h1 h2
    exact piE_greedy I u v h1 h2
  · intro v τ h1 h2
    exact piE_idle I v τ h1 h2

end Opt3
end DelayedSWPT.Extended

open DelayedSWPT.Extended
open DelayedSWPT.Model

theorem solution {n : ℕ} (I : Instance n) :
    IsOptimal (rE I) (pE I) (wE I) (piE I) := by
  exact piE_optimal_core I
