-- Prove2me | solution 1 for CostScaling.Refine.price_increase_le
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T20:28:14.031638+00:00
-- url     : https://prove2.me/submissions/1a6d1c20-dcbd-4b98-930c-f9a59b7ff4f9

import Mathlib
import Definitions.Def_CostScaling_Refine_Run



namespace CostScaling.Refine

open Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma resCap_def (N : Network V) (f : V → V → ℝ) (v w : V) :
    CycleCanceling.MinMean.resCap N f v w = N.u v w - f v w := rfl

lemma rc_antisymm (N : Network V) (p : V → ℝ) {v w : V} (h : (v, w) ∈ N.E) :
    reducedCost N p w v = - reducedCost N p v w := by
  unfold reducedCost
  have := N.cost_antisymm v w h
  linarith

lemma rc_self (N : Network V) (p : V → ℝ) {v : V} (h : (v, v) ∈ N.E) :
    reducedCost N p v v = 0 := by
  have := rc_antisymm N p h
  linarith

lemma excess_eq (N : Network V) (f : V → V → ℝ) (v : V) :
    excess N f v = ∑ y, if (v, y) ∈ N.E then f y v else 0 := by
  unfold excess; rw [Finset.sum_filter]

lemma sum_cross (D : Finset V) (T : V → V → ℝ) (hT : ∀ x y, T x y = - T y x) :
    ∑ x ∈ D, ∑ y ∈ D, T x y = 0 := by
  have h : ∑ x ∈ D, ∑ y ∈ D, T x y = - ∑ x ∈ D, ∑ y ∈ D, T x y := by
    calc ∑ x ∈ D, ∑ y ∈ D, T x y = ∑ y ∈ D, ∑ x ∈ D, T x y := Finset.sum_comm
      _ = ∑ x ∈ D, ∑ y ∈ D, (- T x y) := by
        refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
        exact hT b a
      _ = _ := by simp [Finset.sum_neg_distrib]
  linarith

lemma sum_excess_zero (N : Network V) (f : V → V → ℝ)
    (hf : ∀ v w, (v, w) ∈ N.E → f v w = - f w v) : ∑ v, excess N f v = 0 := by
  simp_rw [excess_eq]
  exact sum_cross Finset.univ (fun x y => if (x, y) ∈ N.E then f y x else 0) (by
    intro x y
    by_cases h : (x, y) ∈ N.E
    · have h' : (y, x) ∈ N.E := (N.symm x y).1 h
      simp only [h, h', if_true]
      have := hf y x h'; linarith
    · have h' : (y, x) ∉ N.E := fun h' => h ((N.symm y x).1 h')
      simp [h, h'])

/-! ### push -/

lemma push_props {N : Network V} {s t : State V} {v w : V} (h : IsPushStep N s v w t) :
    v ≠ w ∧ (v, w) ∈ N.E ∧ 0 < excess N s.f v ∧ 0 < CycleCanceling.MinMean.resCap N s.f v w ∧
      reducedCost N s.p v w < 0 := by
  obtain ⟨⟨hact, ⟨hres, hrc⟩⟩, _, _⟩ := h
  refine ⟨?_, hres.1, hact, hres.2, hrc⟩
  intro hvw
  subst hvw
  have := rc_self N s.p hres.1
  linarith

lemma pushFlow_vw (N : Network V) (s : State V) (v w : V) :
    pushFlow N s v w v w = s.f v w + pushAmount N s v w := by
  unfold pushFlow; simp

lemma pushFlow_wv (N : Network V) (s : State V) {v w : V} (hvw : v ≠ w) :
    pushFlow N s v w w v = s.f w v - pushAmount N s v w := by
  unfold pushFlow
  have : ¬ (w = v ∧ v = w) := fun h => hvw h.2
  simp [this]

lemma pushFlow_other (N : Network V) (s : State V) {v w x y : V}
    (h1 : ¬ (x = v ∧ y = w)) (h2 : ¬ (x = w ∧ y = v)) :
    pushFlow N s v w x y = s.f x y := by
  unfold pushFlow; simp [h1, h2]

lemma push_amt_pos {N : Network V} {s t : State V} {v w : V} (h : IsPushStep N s v w t) :
    0 < pushAmount N s v w := by
  obtain ⟨_, _, he, hr, _⟩ := push_props h
  exact lt_min he hr

lemma push_amt_le_e (N : Network V) (s : State V) (v w : V) :
    pushAmount N s v w ≤ excess N s.f v := min_le_left _ _

lemma push_amt_le_r (N : Network V) (s : State V) (v w : V) :
    pushAmount N s v w ≤ CycleCanceling.MinMean.resCap N s.f v w := min_le_right _ _

lemma push_pseudo {N : Network V} {s t : State V} {v w : V} (h : IsPushStep N s v w t)
    (hps : IsPseudoflow N s.f) : IsPseudoflow N t.f := by
  obtain ⟨hvw, hE, he, hr, hrc⟩ := push_props h
  have htf : t.f = pushFlow N s v w := h.2.1
  have hpos := push_amt_pos h
  have hle := push_amt_le_r N s v w
  rw [resCap_def] at hle
  have hEwv : (w, v) ∈ N.E := (N.symm v w).1 hE
  rw [htf]
  constructor
  · intro x y hxy
    by_cases h1 : x = v ∧ y = w
    · obtain ⟨hx, hy⟩ := h1
      rw [hx, hy, pushFlow_vw]
      linarith
    · by_cases h2 : x = w ∧ y = v
      · obtain ⟨hx, hy⟩ := h2
        rw [hx, hy, pushFlow_wv N s hvw]
        have := hps.1 w v hEwv; linarith
      · rw [pushFlow_other N s h1 h2]; exact hps.1 x y hxy
  · intro x y hxy
    by_cases h1 : x = v ∧ y = w
    · obtain ⟨hx, hy⟩ := h1
      rw [hx, hy, pushFlow_vw, pushFlow_wv N s hvw]
      have := hps.2 v w hE; linarith
    · by_cases h2 : x = w ∧ y = v
      · obtain ⟨hx, hy⟩ := h2
        rw [hx, hy, pushFlow_vw, pushFlow_wv N s hvw]
        have := hps.2 v w hE; linarith
      · have h1' : ¬ (y = v ∧ x = w) := fun h => h2 ⟨h.2, h.1⟩
        have h2' : ¬ (y = w ∧ x = v) := fun h => h1 ⟨h.2, h.1⟩
        rw [pushFlow_other N s h1 h2, pushFlow_other N s h1' h2']
        exact hps.2 x y hxy

lemma push_opt {N : Network V} {ε : ℝ} {s t : State V} {v w : V} (hε : 0 ≤ ε)
    (h : IsPushStep N s v w t) (hopt : IsEpsOptimal N ε s.f s.p) :
    IsEpsOptimal N ε t.f t.p := by
  obtain ⟨hvw, hE, he, hr, hrc⟩ := push_props h
  refine ⟨push_pseudo h hopt.1, ?_⟩
  have htp : t.p = s.p := h.2.2
  have htf : t.f = pushFlow N s v w := h.2.1
  intro x y hres
  rw [htp]
  by_cases h2 : x = w ∧ y = v
  · obtain ⟨hx, hy⟩ := h2
    rw [hx, hy, rc_antisymm N s.p hE]; linarith
  · by_cases h1 : x = v ∧ y = w
    · obtain ⟨hx, hy⟩ := h1
      rw [hx, hy]; exact hopt.2 v w ⟨hE, hr⟩
    · apply hopt.2 x y
      refine ⟨hres.1, ?_⟩
      have h3 := hres.2
      rw [htf, resCap_def, pushFlow_other N s h1 h2, ← resCap_def] at h3
      exact h3

lemma push_excess (N : Network V) (s : State V) {v w : V} (hvw : v ≠ w) (hE : (v, w) ∈ N.E) (u : V) :
    excess N (pushFlow N s v w) u =
      excess N s.f u + (if u = w then pushAmount N s v w else 0)
        - (if u = v then pushAmount N s v w else 0) := by
  rw [excess_eq, excess_eq]
  have hEwv : (w, v) ∈ N.E := (N.symm v w).1 hE
  have : ∀ y, (if (u, y) ∈ N.E then pushFlow N s v w y u else 0) =
      (if (u, y) ∈ N.E then s.f y u else 0)
        + ((if y = v ∧ u = w then pushAmount N s v w else 0)
        - (if y = w ∧ u = v then pushAmount N s v w else 0)) := by
    intro y
    by_cases hy : (u, y) ∈ N.E
    · simp only [hy, if_true]
      by_cases h1 : y = v ∧ u = w
      · obtain ⟨a, b⟩ := h1
        rw [a, b, pushFlow_vw]; simp [hvw, hvw.symm]
      · by_cases h2 : y = w ∧ u = v
        · obtain ⟨a, b⟩ := h2
          rw [a, b, pushFlow_wv N s hvw]
          simp [hvw, hvw.symm]; ring
        · rw [pushFlow_other N s h1 h2]; simp [h1, h2]
    · have h1 : ¬ (y = v ∧ u = w) := by
        rintro ⟨a, b⟩; apply hy; rw [a, b]; exact hEwv
      have h2 : ¬ (y = w ∧ u = v) := by
        rintro ⟨a, b⟩; apply hy; rw [a, b]; exact hE
      simp [hy, h1, h2]
  simp_rw [this]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have e1 : ∑ y : V, (if y = v ∧ u = w then pushAmount N s v w else 0)
      = if u = w then pushAmount N s v w else 0 := by
    by_cases h : u = w <;> simp [h]
  have e2 : ∑ y : V, (if y = w ∧ u = v then pushAmount N s v w else 0)
      = if u = v then pushAmount N s v w else 0 := by
    by_cases h : u = v <;> simp [h]
  rw [e1, e2]; ring

/-! ### relabel -/

lemma relabel_props {N : Network V} {ε : ℝ} {s t : State V} {v : V}
    (h : IsRelabelStep N ε s v t) :
    0 < excess N s.f v ∧ t.f = s.f ∧ (∀ x, x ≠ v → t.p x = s.p x) ∧ s.p v + ε ≤ t.p v := by
  obtain ⟨⟨hact, hall⟩, w0, hw0, hmin, htf, htp⟩ := h
  refine ⟨hact, htf, ?_, ?_⟩
  · intro x hx
    rw [htp]; simp [Function.update_apply, hx]
  · have := hall w0 hw0
    unfold reducedCost at this
    rw [htp]; simp
    linarith

lemma relabel_opt {N : Network V} {ε : ℝ} {s t : State V} {v : V} (hε : 0 ≤ ε)
    (h : IsRelabelStep N ε s v t) (hopt : IsEpsOptimal N ε s.f s.p) :
    IsEpsOptimal N ε t.f t.p := by
  obtain ⟨hprops1, htf', hx', hv'⟩ := relabel_props h
  obtain ⟨⟨hact, hall⟩, w0, hw0, hmin, htf, htp⟩ := h
  have htv : t.p v = s.p w0 + N.c v w0 + ε := by rw [htp]; simp
  rw [htf]
  refine ⟨htf ▸ hopt.1, ?_⟩
  intro x y hres
  have hE := hres.1
  by_cases hx : x = v
  · by_cases hy : y = v
    · rw [hx, hy, rc_self N t.p (by rw [hx, hy] at hE; exact hE)]; linarith
    · have := hmin y (by rw [hx] at hres; exact hres)
      have hty := hx' y hy
      unfold reducedCost
      rw [hx, hty]
      linarith
  · have htx := hx' x hx
    by_cases hy : y = v
    · have := hopt.2 x y hres
      unfold reducedCost at this ⊢
      rw [htx, hy] at *
      linarith
    · have := hopt.2 x y hres
      unfold reducedCost at this ⊢
      rw [htx, hx' y hy]
      exact this

/-! ### initial state -/

lemma initial_pseudo {N : Network V} {f₀ : V → V → ℝ} (p₀ : V → ℝ)
    (hcirc : CycleCanceling.MinMean.IsCirculation N f₀) :
    IsPseudoflow N (initialState N f₀ p₀).f := by
  obtain ⟨hc1, hc2, hc3⟩ := hcirc
  have hcap : ∀ x y, (x, y) ∈ N.E → 0 ≤ N.u x y + N.u y x := by
    intro x y hxy
    have := hc1 x y hxy
    have := hc1 y x ((N.symm x y).1 hxy)
    have := hc2 x y hxy
    linarith
  constructor
  · intro x y hxy
    show initialFlow N f₀ p₀ x y ≤ N.u x y
    unfold initialFlow
    split_ifs with h1 h2
    · exact le_rfl
    · have := hcap x y hxy; linarith
    · exact hc1 x y hxy
  · intro x y hxy
    show initialFlow N f₀ p₀ x y = - initialFlow N f₀ p₀ y x
    have hyx : (y, x) ∈ N.E := (N.symm x y).1 hxy
    have hr := rc_antisymm N p₀ hxy
    unfold initialFlow
    by_cases h1 : reducedCost N p₀ x y < 0
    · have h2 : ¬ reducedCost N p₀ y x < 0 := by rw [hr]; linarith
      simp [hxy, hyx, h1, h2]
    · by_cases h2 : reducedCost N p₀ y x < 0
      · simp [hxy, hyx, h1, h2]
      · simp [hxy, hyx, h1, h2]
        exact hc2 x y hxy

lemma initial_rc_nonneg {N : Network V} {f₀ : V → V → ℝ} (p₀ : V → ℝ) {x y : V}
    (hres : IsResidualArc N (initialState N f₀ p₀).f x y) : 0 ≤ reducedCost N p₀ x y := by
  by_contra hneg
  push_neg at hneg
  have h := hres.2
  have : (initialState N f₀ p₀).f x y = N.u x y := by
    show initialFlow N f₀ p₀ x y = N.u x y
    unfold initialFlow
    simp [hres.1, hneg]
  rw [resCap_def, this] at h
  simp at h

lemma initial_opt {N : Network V} {f₀ : V → V → ℝ} (p₀ : V → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hcirc : CycleCanceling.MinMean.IsCirculation N f₀) :
    IsEpsOptimal N ε (initialState N f₀ p₀).f p₀ := by
  refine ⟨initial_pseudo p₀ hcirc, ?_⟩
  intro x y hres
  have := initial_rc_nonneg p₀ hres
  linarith

/-! ### Lemma 5.1 -/

lemma por_core {V : Type*} [Fintype V] [DecidableEq V]
    (N : Network V) (ε : ℝ) (s : State V)
    (hfeasible : ∃ g, CycleCanceling.MinMean.IsCirculation N g)
    (hopt : IsEpsOptimal N ε s.f s.p) (v : V) (hv : IsActive N s.f v) :
    (∃ w, PushApplicable N s v w) ∨ (∃ t, IsRelabelStep N ε s v t) := by
  by_cases hadm : ∃ w, IsAdmissible N s.f s.p v w
  · obtain ⟨w, hw⟩ := hadm; left; exact ⟨w, hv, hw⟩
  · right
    push_neg at hadm
    have hall : ∀ w, IsResidualArc N s.f v w → 0 ≤ reducedCost N s.p v w := by
      intro w hw
      have := hadm w
      by_contra hneg
      push_neg at hneg
      exact this ⟨hw, hneg⟩
    have hex : ∃ w, IsResidualArc N s.f v w := by
      by_contra hno
      push_neg at hno
      obtain ⟨g, hg1, hg2, hg3⟩ := hfeasible
      have hsat : ∀ y, (v, y) ∈ N.E → s.f v y = N.u v y := by
        intro y hy
        have hle := hopt.1.1 v y hy
        by_contra hne
        apply hno y
        refine ⟨hy, ?_⟩
        rw [resCap_def]
        have := lt_of_le_of_ne hle hne
        linarith
      have h1 : excess N s.f v = ∑ y ∈ Finset.univ.filter (fun y => (v, y) ∈ N.E), (- N.u v y) := by
        unfold excess
        refine Finset.sum_congr rfl (fun y hy => ?_)
        have hy' := (Finset.mem_filter.1 hy).2
        have := hopt.1.2 v y hy'
        have := hsat y hy'
        linarith
      have h2 : ∑ y ∈ Finset.univ.filter (fun y => (v, y) ∈ N.E), g y v = 0 := hg3 v
      have h3 : ∑ y ∈ Finset.univ.filter (fun y => (v, y) ∈ N.E), (- N.u v y)
          ≤ ∑ y ∈ Finset.univ.filter (fun y => (v, y) ∈ N.E), g y v := by
        refine Finset.sum_le_sum (fun y hy => ?_)
        have hy' := (Finset.mem_filter.1 hy).2
        have := hg1 v y hy'
        have := hg2 v y hy'
        linarith
      have : excess N s.f v ≤ 0 := by rw [h1]; linarith
      have hv' : 0 < excess N s.f v := hv
      linarith
    obtain ⟨w1, hw1⟩ := hex
    obtain ⟨w0, hw0S, hmin⟩ := Finset.exists_min_image
      (Finset.univ.filter (fun w => IsResidualArc N s.f v w)) (fun w => s.p w + N.c v w)
      ⟨w1, by simp [hw1]⟩
    have hw0 : IsResidualArc N s.f v w0 := (Finset.mem_filter.1 hw0S).2
    refine ⟨⟨s.f, Function.update s.p v (s.p w0 + N.c v w0 + ε)⟩, ⟨hv, hall⟩, w0, hw0, ?_, rfl, rfl⟩
    intro w hw
    have : s.p w0 + N.c v w0 ≤ s.p w + N.c v w := hmin w (by simp [hw])
    linarith

/-! ### Theorem 5.4 -/

lemma terminated_no_active {N : Network V} {s : State V} (hterm : Terminated N s) (v : V) :
    ¬ IsActive N s.f v := by
  intro hv
  apply hterm.2 v
  refine ⟨hv, ?_⟩
  intro w hw
  by_contra hneg
  push_neg at hneg
  exact hterm.1 v w ⟨hv, hw, hneg⟩

lemma term_core {V : Type*} [Fintype V] [DecidableEq V]
    (N : Network V) (ε : ℝ) (s : State V) (hopt : IsEpsOptimal N ε s.f s.p)
    (hterm : Terminated N s) :
    CycleCanceling.MinMean.IsCirculation N s.f ∧ IsEpsOptimal N ε s.f s.p := by
  refine ⟨⟨hopt.1.1, hopt.1.2, ?_⟩, hopt⟩
  have hle : ∀ v, excess N s.f v ≤ 0 := fun v => not_lt.1 (terminated_no_active hterm v)
  have hsum := sum_excess_zero N s.f hopt.1.2
  have hz := (Finset.sum_eq_zero_iff_of_nonpos (fun v _ => hle v)).1 hsum
  intro w
  exact hz w (Finset.mem_univ w)

/-! ### invariants -/

def Adm (N : Network V) (s : State V) (x y : V) : Prop := IsAdmissible N s.f s.p x y

def Acyc (N : Network V) (s : State V) : Prop :=
  ∀ x y, Relation.ReflTransGen (Adm N s) x y → Relation.ReflTransGen (Adm N s) y x → x = y

structure Inv (N : Network V) (ε : ℝ) (p₀ : V → ℝ) (s : State V) : Prop where
  opt : IsEpsOptimal N ε s.f s.p
  neg : ∀ w, 0 ≤ excess N s.f w ∨ s.p w = p₀ w
  lo : ∀ v, p₀ v ≤ s.p v
  hi : ∀ v, s.p v ≤ p₀ v + 3 * ((Fintype.card V - 1 : ℕ) : ℝ) * ε
  acyc : Acyc N s

lemma bfs_aux (G : V → V → Prop) (q : V → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hG : ∀ x y, G x y → q x ≤ q y + c) (v : V) :
    ∀ j : ℕ, ∃ D : Finset V, v ∈ D ∧ (∀ x ∈ D, q v ≤ q x + j * c) ∧
      ((∀ x ∈ D, ∀ y, G x y → y ∈ D) ∨ j + 1 ≤ D.card) := by
  intro j
  induction j with
  | zero => exact ⟨{v}, by simp, by simp, Or.inr (by simp)⟩
  | succ j ih =>
    obtain ⟨D, hvD, hq, hcl | hcard⟩ := ih
    · refine ⟨D, hvD, fun x hx => ?_, Or.inl hcl⟩
      have := hq x hx
      rw [Nat.cast_succ, add_mul, one_mul]; linarith
    · by_cases hcl : ∀ x ∈ D, ∀ y, G x y → y ∈ D
      · refine ⟨D, hvD, fun x hx => ?_, Or.inl hcl⟩
        have := hq x hx
        rw [Nat.cast_succ, add_mul, one_mul]; linarith
      · refine ⟨D ∪ Finset.univ.filter (fun y => ∃ x ∈ D, G x y), by simp [hvD], ?_, Or.inr ?_⟩
        · intro x hx
          rcases Finset.mem_union.1 hx with hx | hx
          · have := hq x hx
            rw [Nat.cast_succ, add_mul, one_mul]; linarith
          · obtain ⟨x', hx', hG'⟩ := (Finset.mem_filter.1 hx).2
            have := hq x' hx'
            have := hG x' x hG'
            rw [Nat.cast_succ, add_mul, one_mul]; linarith
        · push_neg at hcl
          obtain ⟨x, hx, y, hxy, hy⟩ := hcl
          have hss : D ⊂ D ∪ Finset.univ.filter (fun y => ∃ x ∈ D, G x y) := by
            refine Finset.ssubset_iff_subset_ne.2 ⟨Finset.subset_union_left, ?_⟩
            intro heq
            apply hy
            rw [heq]
            exact Finset.mem_union_right _ (by simp; exact ⟨x, hx, hxy⟩)
          have := Finset.card_lt_card hss
          omega

lemma exists_neg_of_closed {N : Network V} {f f₀ : V → V → ℝ} (hf : IsPseudoflow N f)
    (hcirc : CycleCanceling.MinMean.IsCirculation N f₀) (D : Finset V) {v : V} (hvD : v ∈ D)
    (hv : 0 < excess N f v)
    (hcl : ∀ x ∈ D, ∀ y, (x, y) ∈ N.E ∧ f x y < f₀ x y → y ∈ D) :
    ∃ w ∈ D, excess N f w < 0 := by
  by_contra hno
  push_neg at hno
  have hex0 : ∀ x, excess N f₀ x = 0 := fun x => hcirc.2.2 x
  let T : V → V → ℝ := fun x y => if (x, y) ∈ N.E then f y x - f₀ y x else 0
  have hTanti : ∀ x y, T x y = - T y x := by
    intro x y
    by_cases h : (x, y) ∈ N.E
    · have h' : (y, x) ∈ N.E := (N.symm x y).1 h
      simp only [T, h, h', if_true]
      have := hf.2 x y h
      have := hcirc.2.1 x y h
      linarith
    · have h' : (y, x) ∉ N.E := fun h' => h ((N.symm y x).1 h')
      simp [T, h, h']
  have hdiff : ∀ x, excess N f x = ∑ y, T x y := by
    intro x
    have h0 := hex0 x
    rw [excess_eq] at h0
    rw [excess_eq]
    have : ∑ y, T x y = (∑ y, if (x, y) ∈ N.E then f y x else 0)
        - ∑ y, if (x, y) ∈ N.E then f₀ y x else 0 := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      by_cases h : (x, y) ∈ N.E <;> simp [T, h]
    rw [this, h0, sub_zero]
  have h1 : 0 < ∑ x ∈ D, excess N f x := by
    have := Finset.single_le_sum (f := fun x => excess N f x) (fun x hx => hno x hx) hvD
    linarith
  have h2 : ∑ x ∈ D, excess N f x ≤ 0 := by
    simp_rw [hdiff]
    have hsplit : ∀ x, ∑ y, T x y = ∑ y ∈ D, T x y + ∑ y ∈ Dᶜ, T x y := fun x =>
      (Finset.sum_add_sum_compl D (fun y => T x y)).symm
    simp_rw [hsplit]
    rw [Finset.sum_add_distrib, sum_cross D T hTanti, zero_add]
    refine Finset.sum_nonpos (fun x hx => Finset.sum_nonpos (fun y hy => ?_))
    have hyD : y ∉ D := by simpa using hy
    by_cases h : (x, y) ∈ N.E
    · have : ¬ f x y < f₀ x y := fun hlt => hyD (hcl x hx y ⟨h, hlt⟩)
      push_neg at this
      have h' : (y, x) ∈ N.E := (N.symm x y).1 h
      simp only [T, h, if_true]
      have := hf.2 x y h
      have := hcirc.2.1 x y h
      linarith
    · simp [T, h]
  linarith

lemma active_bound {N : Network V} {ε : ℝ} (hε : 0 < ε) {f₀ : V → V → ℝ} {p₀ : V → ℝ}
    (hcirc : CycleCanceling.MinMean.IsCirculation N f₀) (hentry : IsEpsOptimal N (2 * ε) f₀ p₀)
    {s : State V} (hopt : IsEpsOptimal N ε s.f s.p)
    (hneg : ∀ w, 0 ≤ excess N s.f w ∨ s.p w = p₀ w)
    {v : V} (hv : 0 < excess N s.f v) :
    s.p v ≤ p₀ v + 3 * ((Fintype.card V - 1 : ℕ) : ℝ) * ε := by
  have hG : ∀ x y, ((x, y) ∈ N.E ∧ s.f x y < f₀ x y) →
      (s.p x - p₀ x) ≤ (s.p y - p₀ y) + 3 * ε := by
    rintro x y ⟨hxy, hlt⟩
    have hyx : (y, x) ∈ N.E := (N.symm x y).1 hxy
    have h1 : -ε ≤ reducedCost N s.p x y := by
      apply hopt.2 x y ⟨hxy, ?_⟩
      rw [resCap_def]
      have := hcirc.1 x y hxy
      linarith
    have h2 : -(2 * ε) ≤ reducedCost N p₀ y x := by
      apply hentry.2 y x ⟨hyx, ?_⟩
      rw [resCap_def]
      have := hopt.1.2 x y hxy
      have := hopt.1.1 y x hyx
      have := hcirc.2.1 x y hxy
      linarith
    rw [rc_antisymm N p₀ hxy] at h2
    unfold reducedCost at h1 h2
    linarith
  have hn : 0 < Fintype.card V := Fintype.card_pos_iff.2 ⟨v⟩
  have hfinal : ∀ D : Finset V, v ∈ D →
      (∀ x ∈ D, (s.p v - p₀ v) ≤ (s.p x - p₀ x) + ((Fintype.card V - 1 : ℕ) : ℝ) * (3 * ε)) →
      (∀ x ∈ D, ∀ y, ((x, y) ∈ N.E ∧ s.f x y < f₀ x y) → y ∈ D) →
      s.p v ≤ p₀ v + 3 * ((Fintype.card V - 1 : ℕ) : ℝ) * ε := by
    intro D hvD hq hcl
    obtain ⟨w, hwD, hwneg⟩ := exists_neg_of_closed hopt.1 hcirc D hvD hv hcl
    rcases hneg w with h | h
    · linarith
    · have := hq w hwD
      rw [h] at this
      nlinarith
  obtain ⟨D, hvD, hq, hcl | hcard⟩ := bfs_aux (fun x y => (x, y) ∈ N.E ∧ s.f x y < f₀ x y)
    (fun x => s.p x - p₀ x) (3 * ε) (by linarith) hG v (Fintype.card V - 1)
  · exact hfinal D hvD hq hcl
  · have hD : D = Finset.univ :=
      Finset.eq_univ_of_card D (le_antisymm (Finset.card_le_univ D) (by omega))
    exact hfinal D hvD hq (fun x _ y _ => by rw [hD]; exact Finset.mem_univ y)

/-! ### admissible graph -/

lemma adm_push_sub {N : Network V} {s t : State V} {v w : V} (h : IsPushStep N s v w t)
    {x y : V} (hA : Adm N t x y) : Adm N s x y := by
  obtain ⟨hvw, hE, he, hr, hrc⟩ := push_props h
  have htp : t.p = s.p := h.2.2
  have htf : t.f = pushFlow N s v w := h.2.1
  obtain ⟨⟨hxy, hres⟩, hneg⟩ := hA
  rw [htp] at hneg
  by_cases h2 : x = w ∧ y = v
  · exfalso
    obtain ⟨hx, hy⟩ := h2
    rw [hx, hy, rc_antisymm N s.p hE] at hneg
    linarith
  · by_cases h1 : x = v ∧ y = w
    · obtain ⟨hx, hy⟩ := h1
      rw [hx, hy]; exact ⟨⟨hE, hr⟩, hrc⟩
    · refine ⟨⟨hxy, ?_⟩, hneg⟩
      rw [htf, resCap_def, pushFlow_other N s h1 h2, ← resCap_def] at hres
      exact hres

lemma adm_push_sup {N : Network V} {s t : State V} {v w : V} (h : IsPushStep N s v w t)
    (hnon : 0 < CycleCanceling.MinMean.resCap N t.f v w)
    {x y : V} (hA : Adm N s x y) : Adm N t x y := by
  obtain ⟨hvw, hE, he, hr, hrc⟩ := push_props h
  have htp : t.p = s.p := h.2.2
  have htf : t.f = pushFlow N s v w := h.2.1
  obtain ⟨⟨hxy, hres⟩, hneg⟩ := hA
  by_cases h2 : x = w ∧ y = v
  · exfalso
    obtain ⟨hx, hy⟩ := h2
    rw [hx, hy, rc_antisymm N s.p hE] at hneg
    linarith
  · by_cases h1 : x = v ∧ y = w
    · obtain ⟨hx, hy⟩ := h1
      rw [hx, hy]; exact ⟨⟨hE, hnon⟩, by rw [htp]; exact hrc⟩
    · refine ⟨⟨hxy, ?_⟩, by rw [htp]; exact hneg⟩
      rw [htf, resCap_def, pushFlow_other N s h1 h2, ← resCap_def]
      exact hres

lemma rtg_mono {r p : V → V → Prop} (h : ∀ a b, r a b → p a b) {x y : V}
    (hp : Relation.ReflTransGen r x y) : Relation.ReflTransGen p x y := by
  induction hp with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (h _ _ hbc)

lemma acyc_push {N : Network V} {s t : State V} {v w : V} (h : IsPushStep N s v w t)
    (hac : Acyc N s) : Acyc N t := by
  intro x y hxy hyx
  exact hac x y (rtg_mono (fun a b hab => adm_push_sub h hab) hxy)
    (rtg_mono (fun a b hab => adm_push_sub h hab) hyx)

lemma relabel_no_adm_into {N : Network V} {ε : ℝ} {s t : State V} {v : V} (hε : 0 ≤ ε)
    (h : IsRelabelStep N ε s v t) (hopt : IsEpsOptimal N ε s.f s.p) (x : V) :
    ¬ Adm N t x v := by
  obtain ⟨hp1, htf, hx', hv'⟩ := relabel_props h
  rintro ⟨⟨hE, hres⟩, hneg⟩
  by_cases hx : x = v
  · rw [hx] at hneg hE
    rw [rc_self N t.p hE] at hneg
    exact lt_irrefl _ hneg
  · have h1 := hopt.2 x v ⟨hE, by rw [htf] at hres; exact hres⟩
    unfold reducedCost at h1 hneg
    rw [hx' x hx] at hneg
    linarith

lemma adm_relabel_sub {N : Network V} {ε : ℝ} {s t : State V} {v : V}
    (h : IsRelabelStep N ε s v t) {x y : V} (hx : x ≠ v) (hy : y ≠ v)
    (hA : Adm N t x y) : Adm N s x y := by
  obtain ⟨hp1, htf, hx', hv'⟩ := relabel_props h
  obtain ⟨⟨hE, hres⟩, hneg⟩ := hA
  refine ⟨⟨hE, by rw [htf] at hres; exact hres⟩, ?_⟩
  unfold reducedCost at hneg ⊢
  rw [hx' x hx, hx' y hy] at hneg
  exact hneg

lemma adm_relabel_out {N : Network V} {ε : ℝ} {s t : State V} {v : V}
    (h : IsRelabelStep N ε s v t) (y : V) : ¬ Adm N s v y := by
  obtain ⟨⟨hact, hall⟩, _⟩ := h
  rintro ⟨hres, hneg⟩
  have := hall y hres
  linarith

lemma relabel_path {N : Network V} {ε : ℝ} {s t : State V} {v : V} (hε : 0 ≤ ε)
    (h : IsRelabelStep N ε s v t) (hopt : IsEpsOptimal N ε s.f s.p) {x y : V} (hx : x ≠ v)
    (hp : Relation.ReflTransGen (Adm N t) x y) :
    Relation.ReflTransGen (Adm N s) x y ∧ y ≠ v := by
  induction hp with
  | refl => exact ⟨Relation.ReflTransGen.refl, hx⟩
  | tail hab hbc ih =>
    rename_i b c
    obtain ⟨h1, h2⟩ := ih
    have hc : c ≠ v := fun hc => relabel_no_adm_into hε h hopt b (hc ▸ hbc)
    exact ⟨h1.tail (adm_relabel_sub h h2 hc hbc), hc⟩

lemma acyc_relabel {N : Network V} {ε : ℝ} {s t : State V} {v : V} (hε : 0 ≤ ε)
    (h : IsRelabelStep N ε s v t) (hopt : IsEpsOptimal N ε s.f s.p) (hac : Acyc N s) :
    Acyc N t := by
  intro x y hxy hyx
  by_cases hx : x = v
  · by_cases hy : y = v
    · rw [hx, hy]
    · exfalso; exact (relabel_path hε h hopt hy hyx).2 hx
  · by_cases hy : y = v
    · exfalso; exact (relabel_path hε h hopt hx hxy).2 hy
    · exact hac x y (relabel_path hε h hopt hx hxy).1 (relabel_path hε h hopt hy hyx).1

/-! ### invariant preservation -/

lemma inv_step {N : Network V} {ε : ℝ} (hε : 0 < ε) {f₀ : V → V → ℝ} {p₀ : V → ℝ}
    (hcirc : CycleCanceling.MinMean.IsCirculation N f₀) (hentry : IsEpsOptimal N (2 * ε) f₀ p₀)
    {s t : State V} (hI : Inv N ε p₀ s) (hst : IsStep N ε s t) : Inv N ε p₀ t := by
  rcases hst with ⟨v, w, h⟩ | ⟨v, h⟩
  · obtain ⟨hvw, hE, he, hr, hrc⟩ := push_props h
    have htp : t.p = s.p := h.2.2
    have htf : t.f = pushFlow N s v w := h.2.1
    have hamt := push_amt_pos h
    have hle := push_amt_le_e N s v w
    refine ⟨push_opt hε.le h hI.opt, ?_, ?_, ?_, acyc_push h hI.acyc⟩
    · intro x
      rw [htf, push_excess N s hvw hE x, htp]
      by_cases hxv : x = v
      · left
        have : ¬ x = w := fun h' => hvw (hxv.symm.trans h')
        simp [hxv, hvw]
        linarith
      · by_cases hxw : x = w
        · rcases hI.neg x with h1 | h1
          · left; subst hxw; simp [hxv]; linarith
          · right; exact h1
        · rcases hI.neg x with h1 | h1
          · left; simp [hxw, hxv]; exact h1
          · right; exact h1
    · intro x; rw [htp]; exact hI.lo x
    · intro x; rw [htp]; exact hI.hi x
  · obtain ⟨hp1, htf, hx', hv'⟩ := relabel_props h
    have hopt := relabel_opt hε.le h hI.opt
    have hneg : ∀ x, 0 ≤ excess N t.f x ∨ t.p x = p₀ x := by
      intro x
      rw [htf]
      by_cases hx : x = v
      · left; rw [hx]; exact hp1.le
      · rw [hx' x hx]; exact hI.neg x
    refine ⟨hopt, hneg, ?_, ?_, acyc_relabel hε.le h hI.opt hI.acyc⟩
    · intro x
      by_cases hx : x = v
      · rw [hx]; have := hI.lo v; linarith
      · rw [hx' x hx]; exact hI.lo x
    · intro x
      by_cases hx : x = v
      · rw [hx]
        exact active_bound hε hcirc hentry hopt hneg (by rw [htf]; exact hp1)
      · rw [hx' x hx]; exact hI.hi x

lemma inv_zero {N : Network V} {ε : ℝ} (hε : 0 < ε) {f₀ : V → V → ℝ} (p₀ : V → ℝ)
    (hcirc : CycleCanceling.MinMean.IsCirculation N f₀) :
    Inv N ε p₀ (initialState N f₀ p₀) := by
  refine ⟨initial_opt p₀ hε.le hcirc, fun w => Or.inr rfl, fun v => le_rfl, ?_, ?_⟩
  · intro v
    have : 0 ≤ 3 * ((Fintype.card V - 1 : ℕ) : ℝ) * ε := by positivity
    show p₀ v ≤ _
    linarith
  · have hemp : ∀ x y, ¬ Adm N (initialState N f₀ p₀) x y := by
      intro x y hA
      have := initial_rc_nonneg p₀ hA.1
      have h2 := hA.2
      show False
      have h3 : reducedCost N (initialState N f₀ p₀).p x y < 0 := h2
      have : (initialState N f₀ p₀).p = p₀ := rfl
      rw [this] at h3
      linarith
    have hpath : ∀ x y, Relation.ReflTransGen (Adm N (initialState N f₀ p₀)) x y → x = y := by
      intro x y h
      induction h with
      | refl => rfl
      | tail hab hbc _ => exact absurd hbc (hemp _ _)
    intro x y hxy _
    exact hpath x y hxy

lemma inv_run {N : Network V} {ε : ℝ} (hε : 0 < ε) {f₀ : V → V → ℝ} {p₀ : V → ℝ}
    (hcirc : CycleCanceling.MinMean.IsCirculation N f₀) (hentry : IsEpsOptimal N (2 * ε) f₀ p₀)
    {σ : ℕ → State V} {K : ℕ} (hrun : IsRun N ε f₀ p₀ σ K) :
    ∀ k ≤ K, Inv N ε p₀ (σ k) := by
  intro k
  induction k with
  | zero => intro _; rw [hrun.1]; exact inv_zero hε p₀ hcirc
  | succ k ih =>
    intro hk
    exact inv_step hε hcirc hentry (ih (by omega)) (hrun.2 k (by omega))

/-! ### the first theorems -/

lemma tr_core {V : Type*} [Fintype V] [DecidableEq V]
    (N : Network V) (ε : ℝ) (hε : 0 < ε)
    (f₀ : V → V → ℝ) (p₀ : V → ℝ)
    (hcirc : CycleCanceling.MinMean.IsCirculation N f₀)
    (hentry : IsEpsOptimal N (2 * ε) f₀ p₀)
    (σ : ℕ → State V) (K : ℕ)
    (hrun : IsRun N ε f₀ p₀ σ K)
    (hterm : Terminated N (σ K)) :
    CycleCanceling.MinMean.IsCirculation N (σ K).f ∧
      IsEpsOptimal N ε (σ K).f (σ K).p :=
  term_core N ε (σ K) (inv_run hε hcirc hentry hrun K le_rfl).opt hterm

lemma pi_core {V : Type*} [Fintype V] [DecidableEq V]
    (N : Network V) (ε : ℝ) (hε : 0 < ε)
    (f₀ : V → V → ℝ) (p₀ : V → ℝ)
    (hcirc : CycleCanceling.MinMean.IsCirculation N f₀)
    (hentry : IsEpsOptimal N (2 * ε) f₀ p₀)
    (σ : ℕ → State V) (K : ℕ)
    (hrun : IsRun N ε f₀ p₀ σ K) :
    ∀ k ≤ K, ∀ v, (σ k).p v ≤ p₀ v + 3 * (Fintype.card V : ℝ) * ε := by
  intro k hk v
  have h1 := (inv_run hε hcirc hentry hrun k hk).hi v
  have h2 : ((Fintype.card V - 1 : ℕ) : ℝ) ≤ (Fintype.card V : ℝ) := by
    exact_mod_cast Nat.sub_le _ _
  nlinarith

end CostScaling.Refine

open CostScaling.Refine


theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (N : Network V) (ε : ℝ) (hε : 0 < ε)
    (f₀ : V → V → ℝ) (p₀ : V → ℝ)
    (hcirc : CycleCanceling.MinMean.IsCirculation N f₀)
    (hentry : IsEpsOptimal N (2 * ε) f₀ p₀)
    (σ : ℕ → State V) (K : ℕ)
    (hrun : IsRun N ε f₀ p₀ σ K) :
    ∀ k ≤ K, ∀ v, (σ k).p v ≤ p₀ v + 3 * (Fintype.card V : ℝ) * ε := by
  exact pi_core N ε hε f₀ p₀ hcirc hentry σ K hrun
