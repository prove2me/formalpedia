-- Prove2me | solution 1 for CostScaling.Refine.push_or_relabel_applicable
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T20:23:43.498276+00:00
-- url     : https://prove2.me/submissions/fb3a2583-3981-45ca-9861-25f88a042796

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

lemma initial_opt {N : Network V} {f₀ : V → V → ℝ} (p₀ : V → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hcirc : CycleCanceling.MinMean.IsCirculation N f₀) :
    IsEpsOptimal N ε (initialState N f₀ p₀).f p₀ := by
  refine ⟨initial_pseudo p₀ hcirc, ?_⟩
  intro x y hres
  by_contra hneg
  push_neg at hneg
  have hneg' : reducedCost N p₀ x y < 0 := by linarith
  have h := hres.2
  have : (initialState N f₀ p₀).f x y = N.u x y := by
    show initialFlow N f₀ p₀ x y = N.u x y
    unfold initialFlow
    simp [hres.1, hneg']
  rw [resCap_def, this] at h
  simp at h

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

end CostScaling.Refine

open CostScaling.Refine


theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (N : Network V) (ε : ℝ) (s : State V)
    (hfeasible : ∃ g, CycleCanceling.MinMean.IsCirculation N g)
    (hopt : IsEpsOptimal N ε s.f s.p) (v : V) (hv : IsActive N s.f v) :
    (∃ w, PushApplicable N s v w) ∨ (∃ t, IsRelabelStep N ε s v t) := by
  exact por_core N ε s hfeasible hopt v hv
