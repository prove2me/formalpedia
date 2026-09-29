-- Prove2me | solution 1 for EdmondsKarp.MaxCapacity.maximum_augmentation_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:23:04.495004+00:00
-- url     : https://prove2.me/submissions/d66cd61d-f9ff-48ab-a488-37690fb09fad

import Mathlib
import Definitions.Def_EdmondsKarp_MaxCapacity_Network
import Definitions.Def_EdmondsKarp_MaxCapacity_Augmentation
import Definitions.Def_EdmondsKarp_MaxCapacity_Run

namespace EdmondsKarp.MaxCapacity

set_option linter.unusedSectionVars false

variable {V : Type} [Fintype V] [DecidableEq V]

theorem aux_mab_ite_or (p q : Prop) [Decidable p] [Decidable q] (h : ¬ (p ∧ q)) :
    (if p ∨ q then (1:ℝ) else 0) = (if p then 1 else 0) + (if q then 1 else 0) := by
  by_cases hp : p <;> by_cases hq : q <;> simp_all

theorem aux_mab_pathArcs_cons2 (x y : V) (r : List V) :
    pathArcs (x :: y :: r) = (x, y) :: pathArcs (y :: r) := by
  simp [pathArcs]

theorem aux_mab_mem_pathArcs (P : List V) (a b : V) :
    (a, b) ∈ pathArcs P ↔ ∃ i, P[i]? = some a ∧ P[i+1]? = some b := by
  unfold pathArcs
  rw [List.mem_iff_getElem?]
  simp [List.getElem?_zip_eq_some]

theorem aux_mab_chain_iff (R : V → V → Prop) (P : List V) :
    (∀ e ∈ pathArcs P, R e.1 e.2) ↔ List.IsChain R P := by
  induction P with
  | nil => simp [pathArcs]
  | cons x r ih =>
    cases r with
    | nil => simp [pathArcs]
    | cons y r =>
      rw [aux_mab_pathArcs_cons2, List.isChain_cons_cons, ← ih]
      simp

theorem aux_mab_pathArcs_ne_nil (P : List V) (a b : V) (ha : P.head? = some a)
    (hb : P.getLast? = some b) (hab : a ≠ b) : pathArcs P ≠ [] := by
  match P, ha, hb with
  | [x], ha, hb => simp at ha hb; exact absurd (ha.symm.trans hb) hab
  | x :: y :: r, _, _ => simp [aux_mab_pathArcs_cons2]

theorem aux_mab_not_both (P : List V) (hP : P.Nodup) (x y : V)
    (h1 : (x, y) ∈ pathArcs P) (h2 : (y, x) ∈ pathArcs P) : False := by
  rw [aux_mab_mem_pathArcs] at h1 h2
  obtain ⟨i, hi1, hi2⟩ := h1
  obtain ⟨j, hj1, hj2⟩ := h2
  have hilt : i < P.length := by
    by_contra h; rw [not_lt] at h; rw [List.getElem?_eq_none h] at hi1; simp at hi1
  have hi1lt : i + 1 < P.length := by
    by_contra h; rw [not_lt] at h; rw [List.getElem?_eq_none h] at hi2; simp at hi2
  have e1 : i = j + 1 := (List.getElem?_inj hilt hP).1 (hi1.trans hj2.symm)
  have e2 : i + 1 = j := (List.getElem?_inj hi1lt hP).1 (hi2.trans hj1.symm)
  omega

theorem aux_mab_not_from_last (P : List V) (hP : P.Nodup) (t y : V)
    (ht : P.getLast? = some t) (h : (t, y) ∈ pathArcs P) : False := by
  rw [aux_mab_mem_pathArcs] at h
  obtain ⟨i, hi1, hi2⟩ := h
  have hi1lt : i + 1 < P.length := by
    by_contra h; rw [not_lt] at h; rw [List.getElem?_eq_none h] at hi2; simp at hi2
  rw [List.getLast?_eq_getElem?] at ht
  have hilt : i < P.length := by omega
  have := (List.getElem?_inj hilt hP).1 (hi1.trans ht.symm)
  omega

theorem aux_mab_deg (L : List V) (hL : L.Nodup) (a b : V) (ha : L.head? = some a)
    (hb : L.getLast? = some b) (u : V) :
    ∑ v, ((if (u, v) ∈ pathArcs L then (1:ℝ) else 0) - (if (v, u) ∈ pathArcs L then 1 else 0))
      = (if u = a then 1 else 0) - (if u = b then 1 else 0) := by
  induction L generalizing a with
  | nil => simp at ha
  | cons x r ih =>
    cases r with
    | nil =>
      simp at ha hb; subst ha hb; simp [pathArcs]
    | cons y r =>
      simp at ha; subst ha
      have hnd := hL
      rw [List.nodup_cons] at hnd
      have hy : (y :: r).head? = some y := rfl
      have hb' : (y :: r).getLast? = some b := by simpa using hb
      have ih' := ih hnd.2 y hy hb'
      have hxnot : ∀ w, (x, w) ∉ pathArcs (y :: r) := fun w hw =>
        hnd.1 (List.of_mem_zip hw).1
      have hxnot' : ∀ w, (w, x) ∉ pathArcs (y :: r) := fun w hw => by
        have := (List.of_mem_zip hw).2
        exact hnd.1 (List.mem_of_mem_tail this)
      rw [aux_mab_pathArcs_cons2]
      have key : ∀ v, ((if (u, v) ∈ (x, y) :: pathArcs (y :: r) then (1:ℝ) else 0) -
          (if (v, u) ∈ (x, y) :: pathArcs (y :: r) then 1 else 0)) =
          ((if u = x ∧ v = y then (1:ℝ) else 0) - (if v = x ∧ u = y then 1 else 0)) +
          ((if (u, v) ∈ pathArcs (y :: r) then (1:ℝ) else 0) -
            (if (v, u) ∈ pathArcs (y :: r) then 1 else 0)) := by
        intro v
        have e1 : ((u, v) ∈ (x, y) :: pathArcs (y :: r)) ↔ (u = x ∧ v = y) ∨ (u, v) ∈ pathArcs (y :: r) := by
          simp
        have e2 : ((v, u) ∈ (x, y) :: pathArcs (y :: r)) ↔ (v = x ∧ u = y) ∨ (v, u) ∈ pathArcs (y :: r) := by
          simp
        rw [if_congr e1 rfl rfl, if_congr e2 rfl rfl, aux_mab_ite_or, aux_mab_ite_or]
        · ring
        · rintro ⟨⟨rfl, rfl⟩, h⟩; exact hxnot _ h
        · rintro ⟨⟨rfl, rfl⟩, h⟩; exact hxnot _ h
      rw [Finset.sum_congr rfl (fun v _ => key v), Finset.sum_add_distrib, ih']
      simp [ite_and, Finset.sum_ite_eq', Finset.sum_sub_distrib]

theorem aux_mab_pathEps_spec (N : Network V) (f : V → V → ℝ) (P : List V)
    (hne : pathArcs P ≠ []) :
    (∃ e ∈ pathArcs P, pathEps N f P = stepEps N f e.1 e.2) ∧
      ∀ e ∈ pathArcs P, pathEps N f P ≤ stepEps N f e.1 e.2 := by
  unfold pathEps
  cases h : ((pathArcs P).map (fun e => stepEps N f e.1 e.2)).min? with
  | none =>
    rw [List.min?_eq_none_iff] at h
    simp at h
    exact absurd h hne
  | some m =>
    rw [List.min?_eq_some_iff] at h
    obtain ⟨h1, h2⟩ := h
    simp only [Option.getD_some]
    refine ⟨?_, ?_⟩
    · obtain ⟨e, he, rfl⟩ := List.mem_map.1 h1
      exact ⟨e, he, rfl⟩
    · intro e he
      exact h2 _ (List.mem_map.2 ⟨e, he, rfl⟩)

theorem aux_mab_mem_arcs_of_A (N : Network V) (p : V × V) (h : p ∈ N.A) : p ∈ N.arcs := by
  unfold Network.arcs; exact Finset.mem_insert_of_mem h

theorem aux_mab_ts_mem_arcs (N : Network V) : (N.t, N.s) ∈ N.arcs := by
  unfold Network.arcs; exact Finset.mem_insert_self _ _

theorem aux_mab_stepEps_pos (N : Network V) (f : V → V → ℝ) (hf : IsFlow N f) (x y : V)
    (h : ResArc N f x y) : 0 < stepEps N f x y := by
  unfold stepEps ResArc at *
  by_cases a1 : (x, y) ∈ N.A <;> by_cases a2 : (y, x) ∈ N.A
  · have h1 := hf.2.1 x y a1
    have h2 := hf.1 y x (aux_mab_mem_arcs_of_A N _ a2)
    simp only [a1, a2, if_true, true_and] at h ⊢
    rcases h with h | h <;> linarith
  · simp only [a1, a2, if_true, if_false, true_and, false_and, or_false] at h ⊢
    exact h
  · simp only [a1, a2, if_true, if_false, true_and, false_and, false_or] at h ⊢
    exact h
  · simp [a1, a2] at h

theorem aux_mab_minmax (ε c f : ℝ) : min ε (c - f) + max 0 (ε - c + f) = ε := by
  rcases le_total ε (c - f) with h | h
  · rw [min_eq_left h, max_eq_left (by linarith)]; ring
  · rw [min_eq_right h, max_eq_right (by linarith)]; ring

theorem aux_mab_D_generic (N : Network V) (f : V → V → ℝ) (P : List V)
    (hnd : P.Nodup) (hres : ∀ e ∈ pathArcs P, ResArc N f e.1 e.2) (x y : V)
    (h1 : ¬ (x = N.t ∧ y = N.s)) (h2 : ¬ (y = N.t ∧ x = N.s)) :
    (if (x, y) ∈ N.arcs then augment N f P x y - f x y else 0) -
      (if (y, x) ∈ N.arcs then augment N f P y x - f y x else 0) =
    pathEps N f P * (((if (x, y) ∈ pathArcs P then 1 else 0) + (if x = N.t ∧ y = N.s then 1 else 0)) -
      ((if (y, x) ∈ pathArcs P then 1 else 0) + (if y = N.t ∧ x = N.s then 1 else 0))) := by
  have hxy : (x, y) ∈ N.arcs ↔ (x, y) ∈ N.A := by
    simp [Network.arcs, Prod.ext_iff, h1]
  have hyx : (y, x) ∈ N.arcs ↔ (y, x) ∈ N.A := by
    simp [Network.arcs, Prod.ext_iff, h2]
  rw [if_congr hxy rfl rfl, if_congr hyx rfl rfl, if_neg h1, if_neg h2]
  simp only [augment, if_neg h1, if_neg h2, augIncrease, augDecrease]
  have hr1 : (x, y) ∈ pathArcs P → (x, y) ∈ N.A ∨ (y, x) ∈ N.A := fun h => by
    rcases hres _ h with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  have hr2 : (y, x) ∈ pathArcs P → (y, x) ∈ N.A ∨ (x, y) ∈ N.A := fun h => by
    rcases hres _ h with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  have hnb := aux_mab_not_both P hnd x y
  have hmm := aux_mab_minmax (pathEps N f P) (N.c x y) (f x y)
  have hmm' := aux_mab_minmax (pathEps N f P) (N.c y x) (f y x)
  by_cases a1 : (x, y) ∈ N.A <;> by_cases a2 : (y, x) ∈ N.A <;>
    by_cases p1 : (x, y) ∈ pathArcs P <;> by_cases p2 : (y, x) ∈ pathArcs P <;>
    simp only [a1, a2, p1, p2, if_true, if_false] <;>
    first
    | linarith
    | (exfalso; tauto)

theorem aux_mab_D_ts (N : Network V) (f : V → V → ℝ) (P : List V)
    (hnd : P.Nodup) (hlt : P.getLast? = some N.t)
    (hres : ∀ e ∈ pathArcs P, ResArc N f e.1 e.2) :
    (if (N.t, N.s) ∈ N.arcs then augment N f P N.t N.s - f N.t N.s else 0) -
      (if (N.s, N.t) ∈ N.arcs then augment N f P N.s N.t - f N.s N.t else 0) =
    pathEps N f P * (((if (N.t, N.s) ∈ pathArcs P then 1 else 0) +
      (if N.t = N.t ∧ N.s = N.s then 1 else 0)) -
      ((if (N.s, N.t) ∈ pathArcs P then 1 else 0) + (if N.s = N.t ∧ N.t = N.s then 1 else 0))) := by
  have hst := N.source_ne_sink
  have hts1 : (N.t, N.s) ∉ pathArcs P := fun h => aux_mab_not_from_last P hnd N.t N.s hlt h
  have hsA : (N.s, N.t) ∈ N.arcs ↔ (N.s, N.t) ∈ N.A := by
    simp [Network.arcs, Prod.ext_iff, hst]
  have hret := N.return_not_mem
  rw [if_pos (aux_mab_ts_mem_arcs N), if_congr hsA rfl rfl]
  simp only [augment, augIncrease, augDecrease, and_self, if_true, hts1, if_false, hret,
    hst, false_and]
  by_cases a1 : (N.s, N.t) ∈ N.A
  · by_cases p1 : (N.s, N.t) ∈ pathArcs P <;> simp [a1, p1]
  · have p1 : (N.s, N.t) ∉ pathArcs P := by
      intro h
      rcases hres _ h with h | h
      · exact a1 h.1
      · exact hret h.1
    simp [a1, p1]

theorem aux_mab_D (N : Network V) (f : V → V → ℝ) (P : List V)
    (hnd : P.Nodup) (hlt : P.getLast? = some N.t)
    (hres : ∀ e ∈ pathArcs P, ResArc N f e.1 e.2) (x y : V) :
    (if (x, y) ∈ N.arcs then augment N f P x y - f x y else 0) -
      (if (y, x) ∈ N.arcs then augment N f P y x - f y x else 0) =
    pathEps N f P * (((if (x, y) ∈ pathArcs P then 1 else 0) + (if x = N.t ∧ y = N.s then 1 else 0)) -
      ((if (y, x) ∈ pathArcs P then 1 else 0) + (if y = N.t ∧ x = N.s then 1 else 0))) := by
  by_cases h1 : x = N.t ∧ y = N.s
  · obtain ⟨rfl, rfl⟩ := h1
    exact aux_mab_D_ts N f P hnd hlt hres
  by_cases h2 : y = N.t ∧ x = N.s
  · obtain ⟨rfl, rfl⟩ := h2
    have := aux_mab_D_ts N f P hnd hlt hres
    linarith
  exact aux_mab_D_generic N f P hnd hres x y h1 h2

theorem aux_mab_augment_flow (N : Network V) (f : V → V → ℝ) (P : List V)
    (hf : IsFlow N f) (hP : IsAugPath N f P) : IsFlow N (augment N f P) := by
  obtain ⟨hnd, hhd, hlt, hres⟩ := hP
  have hne := aux_mab_pathArcs_ne_nil P N.s N.t hhd hlt N.source_ne_sink
  obtain ⟨⟨e0, he0, hε0⟩, hεle⟩ := aux_mab_pathEps_spec N f P hne
  have hεpos : 0 < pathEps N f P := hε0 ▸ aux_mab_stepEps_pos N f hf _ _ (hres e0 he0)
  have hret := N.return_not_mem
  refine ⟨?_, ?_, ?_⟩
  · intro u v huv
    rcases Finset.mem_insert.1 huv with h | h
    · obtain ⟨rfl, rfl⟩ := Prod.ext_iff.1 h
      have := hf.1 _ _ huv
      simp only [augment, and_self, if_true]
      linarith
    · have hne' : ¬ (u = N.t ∧ v = N.s) := by
        rintro ⟨rfl, rfl⟩; exact hret h
      have hf0 := hf.1 u v huv
      have hfc := hf.2.1 u v h
      simp only [augment, if_neg hne', if_pos h, augIncrease, augDecrease]
      by_cases p1 : (u, v) ∈ pathArcs P
      · have p2 : (v, u) ∉ pathArcs P := fun p2 => aux_mab_not_both P hnd u v p1 p2
        simp only [p1, p2, if_true, if_false]
        split_ifs
        · have := le_min hεpos.le (sub_nonneg.2 hfc)
          linarith
        · linarith
      · by_cases p2 : (v, u) ∈ pathArcs P
        · have he := hεle _ p2
          simp only [stepEps, h, if_true] at he
          simp only [p1, p2, if_true, if_false]
          split_ifs with a2
          · simp only [a2, if_true] at he
            have : max 0 (pathEps N f P - N.c v u + f v u) ≤ f u v :=
              max_le hf0 (by linarith)
            linarith
          · simp only [a2, if_false] at he
            linarith
        · simp only [p1, p2, if_false]
          linarith
  · intro u v h
    have hne' : ¬ (u = N.t ∧ v = N.s) := by
      rintro ⟨rfl, rfl⟩; exact hret h
    have hfc := hf.2.1 u v h
    simp only [augment, if_neg hne', if_pos h, augIncrease, augDecrease]
    by_cases p1 : (u, v) ∈ pathArcs P
    · have p2 : (v, u) ∉ pathArcs P := fun p2 => aux_mab_not_both P hnd u v p1 p2
      have he := hεle _ p1
      simp only [stepEps, h, if_true] at he
      simp only [p1, p2, if_true, if_false]
      split_ifs with a2
      · have := min_le_right (pathEps N f P) (N.c u v - f u v)
        linarith
      · simp only [a2, if_false] at he
        linarith
    · by_cases p2 : (v, u) ∈ pathArcs P
      · simp only [p1, p2, if_true, if_false]
        split_ifs
        · have := le_max_left 0 (pathEps N f P - N.c v u + f v u)
          linarith
        · linarith
      · simp only [p1, p2, if_false]
        linarith
  · intro u
    have hfc := hf.2.2 u
    rw [Finset.sum_filter, Finset.sum_filter] at hfc ⊢
    have e1 : ∀ v, (if (u, v) ∈ N.arcs then augment N f P u v else 0) =
        (if (u, v) ∈ N.arcs then f u v else 0) +
          (if (u, v) ∈ N.arcs then augment N f P u v - f u v else 0) := by
      intro v; split_ifs <;> ring
    have e2 : ∀ v, (if (v, u) ∈ N.arcs then augment N f P v u else 0) =
        (if (v, u) ∈ N.arcs then f v u else 0) +
          (if (v, u) ∈ N.arcs then augment N f P v u - f v u else 0) := by
      intro v; split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun v _ => e1 v), Finset.sum_congr rfl (fun v _ => e2 v),
      Finset.sum_add_distrib, Finset.sum_add_distrib]
    have hD : ∑ v, ((if (u, v) ∈ N.arcs then augment N f P u v - f u v else 0) -
        (if (v, u) ∈ N.arcs then augment N f P v u - f v u else 0)) = 0 := by
      rw [Finset.sum_congr rfl (fun v _ => aux_mab_D N f P hnd hlt hres u v), ← Finset.mul_sum]
      have hdeg := aux_mab_deg P hnd N.s N.t hhd hlt u
      have : ∑ v, (((if (u, v) ∈ pathArcs P then (1:ℝ) else 0) + (if u = N.t ∧ v = N.s then 1 else 0)) -
          ((if (v, u) ∈ pathArcs P then 1 else 0) + (if v = N.t ∧ u = N.s then 1 else 0))) = 0 := by
        have r : ∀ v, (((if (u, v) ∈ pathArcs P then (1:ℝ) else 0) + (if u = N.t ∧ v = N.s then 1 else 0)) -
          ((if (v, u) ∈ pathArcs P then 1 else 0) + (if v = N.t ∧ u = N.s then 1 else 0))) =
          ((if (u, v) ∈ pathArcs P then (1:ℝ) else 0) - (if (v, u) ∈ pathArcs P then 1 else 0)) +
          ((if u = N.t ∧ v = N.s then 1 else 0) - (if v = N.t ∧ u = N.s then 1 else 0)) := by
          intro v; ring
        rw [Finset.sum_congr rfl (fun v _ => r v), Finset.sum_add_distrib, hdeg,
          Finset.sum_sub_distrib]
        simp only [ite_and, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        by_cases hu : u = N.t <;> simp [hu]
      rw [this, mul_zero]
    rw [Finset.sum_sub_distrib] at hD
    linarith

theorem aux_mab_Z_add {a b : ℝ} (ha : ∃ z : ℤ, a = z) (hb : ∃ z : ℤ, b = z) :
    ∃ z : ℤ, a + b = z := by
  obtain ⟨x, rfl⟩ := ha; obtain ⟨y, rfl⟩ := hb; exact ⟨x + y, by push_cast; ring⟩

theorem aux_mab_Z_sub {a b : ℝ} (ha : ∃ z : ℤ, a = z) (hb : ∃ z : ℤ, b = z) :
    ∃ z : ℤ, a - b = z := by
  obtain ⟨x, rfl⟩ := ha; obtain ⟨y, rfl⟩ := hb; exact ⟨x - y, by push_cast; ring⟩

theorem aux_mab_Z_min {a b : ℝ} (ha : ∃ z : ℤ, a = z) (hb : ∃ z : ℤ, b = z) :
    ∃ z : ℤ, min a b = z := by
  obtain ⟨x, rfl⟩ := ha; obtain ⟨y, rfl⟩ := hb; exact ⟨min x y, by push_cast; ring⟩

theorem aux_mab_Z_max {a b : ℝ} (ha : ∃ z : ℤ, a = z) (hb : ∃ z : ℤ, b = z) :
    ∃ z : ℤ, max a b = z := by
  obtain ⟨x, rfl⟩ := ha; obtain ⟨y, rfl⟩ := hb; exact ⟨max x y, by push_cast; ring⟩

theorem aux_mab_Z_zero : ∃ z : ℤ, (0 : ℝ) = z := ⟨0, by simp⟩

theorem aux_mab_augment_int (N : Network V) (f : V → V → ℝ) (P : List V)
    (hcap : IntegralCaps N) (hfi : IsIntegralOn N f) (hP : IsAugPath N f P) :
    (∃ z : ℤ, pathEps N f P = z) ∧ IsIntegralOn N (augment N f P) := by
  obtain ⟨hnd, hhd, hlt, hres⟩ := hP
  have hne := aux_mab_pathArcs_ne_nil P N.s N.t hhd hlt N.source_ne_sink
  obtain ⟨⟨e0, he0, hε0⟩, -⟩ := aux_mab_pathEps_spec N f P hne
  have hcZ : ∀ x y, (x, y) ∈ N.A → ∃ z : ℤ, N.c x y = z := fun x y h => hcap (x, y) h
  have hfZ : ∀ x y, (x, y) ∈ N.A → ∃ z : ℤ, f x y = z := fun x y h =>
    hfi (x, y) (aux_mab_mem_arcs_of_A N _ h)
  have hstepZ : ∀ x y, ResArc N f x y → ∃ z : ℤ, stepEps N f x y = z := by
    intro x y hr
    unfold stepEps
    split_ifs with a1 a2
    · exact aux_mab_Z_add (aux_mab_Z_sub (hcZ x y a1) (hfZ x y a1)) (hfZ y x a2)
    · exact aux_mab_Z_sub (hcZ x y a1) (hfZ x y a1)
    · rcases hr with hr | hr
      · exact absurd hr.1 a1
      · exact hfZ y x hr.1
  have hεZ : ∃ z : ℤ, pathEps N f P = z := hε0 ▸ hstepZ _ _ (hres e0 he0)
  refine ⟨hεZ, ?_⟩
  rintro ⟨x, y⟩ hp
  rcases Finset.mem_insert.1 hp with h | h
  · obtain ⟨rfl, rfl⟩ := Prod.ext_iff.1 h
    simp only [augment, and_self, if_true]
    exact aux_mab_Z_add (hfi _ (aux_mab_ts_mem_arcs N)) hεZ
  · have hne' : ¬ (x = N.t ∧ y = N.s) := by
      rintro ⟨rfl, rfl⟩; exact N.return_not_mem h
    simp only [augment, if_neg hne', if_pos h, augIncrease, augDecrease]
    refine aux_mab_Z_sub (aux_mab_Z_add (hfZ x y h) ?_) ?_
    · split_ifs
      · exact aux_mab_Z_min hεZ (aux_mab_Z_sub (hcZ x y h) (hfZ x y h))
      · exact hεZ
      · exact aux_mab_Z_zero
    · split_ifs with p2 a2
      · exact aux_mab_Z_max aux_mab_Z_zero
          (aux_mab_Z_add (aux_mab_Z_sub hεZ (hcZ y x a2)) (hfZ y x a2))
      · exact hεZ
      · exact aux_mab_Z_zero

theorem aux_mab_cut_identity (N : Network V) (h : V → V → ℝ)
    (hcons : ∀ u, (∑ v ∈ Finset.univ.filter (fun v => (u, v) ∈ N.arcs), h u v) -
      (∑ v ∈ Finset.univ.filter (fun v => (v, u) ∈ N.arcs), h v u) = 0)
    (X : Finset V) (hs : N.s ∈ X) (ht : N.t ∉ X) :
    h N.t N.s = cutFlowOut N h X - cutFlowIn N h X := by
  have h0 : ∑ u ∈ X, ((∑ v ∈ Finset.univ.filter (fun v => (u, v) ∈ N.arcs), h u v) -
      (∑ v ∈ Finset.univ.filter (fun v => (v, u) ∈ N.arcs), h v u)) = 0 :=
    Finset.sum_eq_zero (fun u _ => hcons u)
  have hout : ∑ u ∈ X, (∑ v ∈ Finset.univ.filter (fun v => (u, v) ∈ N.arcs), h u v) =
      ∑ p ∈ N.arcs, (if p.1 ∈ X then h p.1 p.2 else 0) := by
    rw [← Finset.sum_ite_mem_eq N.arcs, Fintype.sum_prod_type, ← Finset.sum_ite_mem_eq X]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [Finset.sum_filter]
    split_ifs with hu
    · simp
    · simp
  have hin : ∑ u ∈ X, (∑ v ∈ Finset.univ.filter (fun v => (v, u) ∈ N.arcs), h v u) =
      ∑ p ∈ N.arcs, (if p.2 ∈ X then h p.1 p.2 else 0) := by
    rw [← Finset.sum_ite_mem_eq N.arcs, Fintype.sum_prod_type, Finset.sum_comm,
      ← Finset.sum_ite_mem_eq X]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [Finset.sum_filter]
    split_ifs with hu
    · simp
    · simp
  rw [Finset.sum_sub_distrib, hout, hin, ← Finset.sum_sub_distrib] at h0
  unfold Network.arcs at h0
  rw [Finset.sum_insert N.return_not_mem] at h0
  simp only [hs, ht, if_true, if_false] at h0
  have hA : ∑ p ∈ N.A, ((if p.1 ∈ X then h p.1 p.2 else 0) - (if p.2 ∈ X then h p.1 p.2 else 0))
      = cutFlowOut N h X - cutFlowIn N h X := by
    unfold cutFlowOut cutFlowIn
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    by_cases h1 : p.1 ∈ X <;> by_cases h2 : p.2 ∈ X <;> simp [h1, h2]
  linarith

theorem aux_mab_cut_bound (N : Network V) (M : ℕ) (hcross : CrossArcsBounded N M)
    (f h : V → V → ℝ) (hf : IsFlow N f) (hh : IsFlow N h) (θ : ℝ) (hθ : 0 ≤ θ)
    (X : Finset V) (hs : N.s ∈ X) (ht : N.t ∉ X)
    (hcl : ∀ u ∈ X, ∀ v, ResArc N f u v → θ < stepEps N f u v → v ∈ X) :
    h N.t N.s - f N.t N.s ≤ M * θ := by
  rw [aux_mab_cut_identity N h hh.2.2 X hs ht, aux_mab_cut_identity N f hf.2.2 X hs ht]
  set Aout := N.A.filter (fun p => p.1 ∈ X ∧ p.2 ∉ X) with hAout
  set Ain := N.A.filter (fun p => p.1 ∉ X ∧ p.2 ∈ X) with hAin
  have h1 : cutFlowOut N h X ≤ ∑ p ∈ Aout, N.c p.1 p.2 := by
    unfold cutFlowOut
    exact Finset.sum_le_sum (fun p hp => hh.2.1 p.1 p.2 (Finset.mem_filter.1 hp).1)
  have h2 : 0 ≤ cutFlowIn N h X := by
    unfold cutFlowIn
    exact Finset.sum_nonneg (fun p hp =>
      hh.1 p.1 p.2 (aux_mab_mem_arcs_of_A N _ (Finset.mem_filter.1 hp).1))
  have h3 : ∑ p ∈ Aout, N.c p.1 p.2 - cutFlowOut N f X ≤ Aout.card • θ := by
    unfold cutFlowOut
    rw [← hAout, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_card_nsmul
    intro p hp
    obtain ⟨hpA, hu, hv⟩ := Finset.mem_filter.1 hp
    by_contra hlt
    rw [not_le] at hlt
    have hr : ResArc N f p.1 p.2 := Or.inl ⟨hpA, by linarith⟩
    have hge : N.c p.1 p.2 - f p.1 p.2 ≤ stepEps N f p.1 p.2 := by
      unfold stepEps
      rw [if_pos hpA]
      split_ifs with a2
      · linarith [hf.1 p.2 p.1 (aux_mab_mem_arcs_of_A N _ a2)]
      · exact le_rfl
    exact hv (hcl p.1 hu p.2 hr (by linarith))
  have h4 : cutFlowIn N f X ≤ Ain.card • θ := by
    unfold cutFlowIn
    rw [← hAin]
    apply Finset.sum_le_card_nsmul
    intro p hp
    obtain ⟨hpA, hv, hu⟩ := Finset.mem_filter.1 hp
    by_contra hlt
    rw [not_le] at hlt
    have hr : ResArc N f p.2 p.1 := Or.inr ⟨hpA, by linarith⟩
    have hge : f p.1 p.2 ≤ stepEps N f p.2 p.1 := by
      unfold stepEps
      split_ifs with a1
      · linarith [hf.2.1 p.2 p.1 a1]
      · exact le_rfl
    exact hv (hcl p.2 hu p.1 hr (by linarith))
  have h5 : Aout.card + Ain.card ≤ M := by
    have hdis : Disjoint Aout Ain := by
      rw [Finset.disjoint_left]
      intro p h1 h2
      exact (Finset.mem_filter.1 h2).2.1 (Finset.mem_filter.1 h1).2.1
    rw [← Finset.card_union_of_disjoint hdis]
    refine le_trans (Finset.card_le_card ?_) (hcross X hs ht)
    intro p hp
    unfold Network.arcs
    rcases Finset.mem_union.1 hp with hp | hp
    · obtain ⟨hpA, h1, h2⟩ := Finset.mem_filter.1 hp
      exact Finset.mem_filter.2 ⟨Finset.mem_insert_of_mem hpA, Or.inl ⟨h1, h2⟩⟩
    · obtain ⟨hpA, h1, h2⟩ := Finset.mem_filter.1 hp
      exact Finset.mem_filter.2 ⟨Finset.mem_insert_of_mem hpA, Or.inr ⟨h1, h2⟩⟩
  have h5' : ((Aout.card : ℝ) + Ain.card) ≤ M := by exact_mod_cast h5
  rw [nsmul_eq_mul] at h3 h4
  nlinarith

theorem aux_mab_noaug_bound (N : Network V) (M : ℕ) (hcross : CrossArcsBounded N M)
    (f : V → V → ℝ) (hf : IsFlow N f) (θ : ℝ) (hθ : 0 ≤ θ)
    (hno : ∀ Q : List V, IsAugPath N f Q → pathEps N f Q ≤ θ)
    (h : V → V → ℝ) (hh : IsFlow N h) :
    h N.t N.s - f N.t N.s ≤ M * θ := by
  classical
  let R : V → V → Prop := fun x y => ResArc N f x y ∧ θ < stepEps N f x y
  let X : Finset V := Finset.univ.filter (fun v => ∃ Q : List V, Q.Nodup ∧
    Q.head? = some N.s ∧ Q.getLast? = some v ∧ List.IsChain R Q)
  refine aux_mab_cut_bound N M hcross f h hf hh θ hθ X ?_ ?_ ?_
  · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, [N.s], List.nodup_singleton _, rfl, rfl,
      List.isChain_singleton _⟩
  · intro htX
    obtain ⟨Q, hnd, hhd, hlt, hc⟩ := (Finset.mem_filter.1 htX).2
    have hc' := (aux_mab_chain_iff R Q).2 hc
    have hQ : IsAugPath N f Q := ⟨hnd, hhd, hlt, fun e he => (hc' e he).1⟩
    have hne := aux_mab_pathArcs_ne_nil Q N.s N.t hhd hlt N.source_ne_sink
    obtain ⟨⟨e0, he0, hε0⟩, -⟩ := aux_mab_pathEps_spec N f Q hne
    have := hno Q hQ
    have := (hc' e0 he0).2
    linarith
  · intro u hu v hr hθv
    obtain ⟨Q, hnd, hhd, hlt, hc⟩ := (Finset.mem_filter.1 hu).2
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    by_cases hv : v ∈ Q
    · obtain ⟨L1, L2, rfl⟩ := List.append_of_mem hv
      have e : L1 ++ v :: L2 = (L1 ++ [v]) ++ L2 := by simp
      rw [e] at hnd hhd hc
      refine ⟨L1 ++ [v], hnd.sublist (List.sublist_append_left _ _), ?_, by simp,
        hc.left_of_append⟩
      rw [List.head?_append] at hhd ⊢
      cases L1 with
      | nil => simpa using hhd
      | cons a l => simpa using hhd
    · refine ⟨Q ++ [v], ?_, ?_, by simp, ?_⟩
      · rw [List.nodup_append]
        refine ⟨hnd, List.nodup_singleton _, ?_⟩
        intro a ha b hb
        simp only [List.mem_singleton] at hb
        subst hb
        rintro rfl
        exact hv ha
      · rw [List.head?_append, hhd]; rfl
      · refine hc.append (List.isChain_singleton _) ?_
        intro x hx y hy
        rw [hlt] at hx
        simp only [Option.mem_def, Option.some.injEq] at hx
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
        subst hx hy
        exact ⟨hr, hθv⟩

end EdmondsKarp.MaxCapacity

open EdmondsKarp.MaxCapacity

theorem solution {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (hcap : IntegralCaps N) (M : ℕ) (hM : 1 < M) (hcross : CrossArcsBounded N M)
    (g : V → V → ℝ) (hg : IsMaxFlow N g)
    (K : ℕ) (f : ℕ → V → V → ℝ) (P : ℕ → List V) (hrun : IsMaxAugRun N K f P)
    (hint : IsIntegralOn N (f 0)) :
    (K : ℝ) ≤ 1 + Real.logb ((M : ℝ) / ((M : ℝ) - 1)) (g N.t N.s) ∧
      ((¬ ∃ Q : List V, IsAugPath N (f K) Q) → IsMaxFlow N (f K)) := by
  obtain ⟨hf0, hstep⟩ := hrun
  have hM' : (1 : ℝ) < M := by exact_mod_cast hM
  have hMpos : (0 : ℝ) < M := by linarith
  have hFI : ∀ k ≤ K, IsFlow N (f k) ∧ IsIntegralOn N (f k) := by
    intro k
    induction k with
    | zero => intro _; exact ⟨hf0, hint⟩
    | succ k ih =>
      intro hk
      obtain ⟨hfk, hik⟩ := ih (by omega)
      obtain ⟨hmax, hfeq⟩ := hstep k (by omega)
      rw [hfeq]
      exact ⟨aux_mab_augment_flow N (f k) (P k) hfk hmax.1,
        (aux_mab_augment_int N (f k) (P k) hcap hik hmax.1).2⟩
  -- an augmenting path relative to an integral flow has `ε ≥ 1`
  have hεge1 : ∀ (h : V → V → ℝ) (Q : List V), IsFlow N h → IsIntegralOn N h →
      IsAugPath N h Q → 1 ≤ pathEps N h Q := by
    intro h Q hh hi hQ
    obtain ⟨z, hz⟩ := (aux_mab_augment_int N h Q hcap hi hQ).1
    obtain ⟨hnd, hhd, hlt, hres⟩ := hQ
    have hne := aux_mab_pathArcs_ne_nil Q N.s N.t hhd hlt N.source_ne_sink
    obtain ⟨⟨e0, he0, hε0⟩, -⟩ := aux_mab_pathEps_spec N h Q hne
    have hpos : 0 < pathEps N h Q := hε0 ▸ aux_mab_stepEps_pos N h hh _ _ (hres e0 he0)
    rw [hz] at hpos ⊢
    have : (0 : ℤ) < z := by exact_mod_cast hpos
    have : (1 : ℤ) ≤ z := this
    exact_mod_cast this
  have hval : ∀ k < K, f (k + 1) N.t N.s = f k N.t N.s + pathEps N (f k) (P k) := by
    intro k hk
    rw [(hstep k hk).2]
    simp [augment]
  have hε1 : ∀ k < K, 1 ≤ pathEps N (f k) (P k) := fun k hk =>
    hεge1 _ _ (hFI k hk.le).1 (hFI k hk.le).2 (hstep k hk).1.1
  have hdec : ∀ k < K, g N.t N.s - f k N.t N.s ≤ M * pathEps N (f k) (P k) := fun k hk =>
    aux_mab_noaug_bound N M hcross (f k) (hFI k hk.le).1 _ (by linarith [hε1 k hk])
      (hstep k hk).1.2 g hg.1
  set q : ℝ := 1 - 1 / M with hq
  have hq0 : 0 ≤ q := by
    rw [hq, sub_nonneg, div_le_one hMpos]; linarith
  have hr : ∀ k ≤ K, g N.t N.s - f k N.t N.s ≤ q ^ k * (g N.t N.s - f 0 N.t N.s) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have ih' := ih (by omega)
      have hv := hval k (by omega)
      have hd := hdec k (by omega)
      have h1 : (g N.t N.s - f k N.t N.s) / M ≤ pathEps N (f k) (P k) := by
        rw [div_le_iff₀ hMpos]; linarith
      have h2 : g N.t N.s - f (k + 1) N.t N.s ≤ q * (g N.t N.s - f k N.t N.s) := by
        rw [hv, hq]
        have : (1 - 1 / (M:ℝ)) * (g N.t N.s - f k N.t N.s) =
            (g N.t N.s - f k N.t N.s) - (g N.t N.s - f k N.t N.s) / M := by
          field_simp
        rw [this]; linarith
      calc g N.t N.s - f (k + 1) N.t N.s ≤ q * (g N.t N.s - f k N.t N.s) := h2
        _ ≤ q * (q ^ k * (g N.t N.s - f 0 N.t N.s)) := mul_le_mul_of_nonneg_left ih' hq0
        _ = q ^ (k + 1) * (g N.t N.s - f 0 N.t N.s) := by ring
  have hf0ts : 0 ≤ f 0 N.t N.s := hf0.1 _ _ (aux_mab_ts_mem_arcs N)
  have hb1 : (1 : ℝ) < (M : ℝ) / ((M : ℝ) - 1) := by
    rw [one_lt_div (by linarith)]; linarith
  refine ⟨?_, ?_⟩
  · rcases Nat.eq_zero_or_pos K with hK | hK
    · subst hK
      simp only [Nat.cast_zero]
      suffices hlog : 0 ≤ Real.logb ((M : ℝ) / ((M : ℝ) - 1)) (g N.t N.s) by linarith
      by_cases hex : ∃ Q : List V, IsAugPath N (f 0) Q
      · obtain ⟨Q, hQ⟩ := hex
        have hfl := aux_mab_augment_flow N (f 0) Q hf0 hQ
        have h1 := hεge1 _ _ hf0 hint hQ
        have h2 := hg.2 _ hfl
        have h3 : augment N (f 0) Q N.t N.s = f 0 N.t N.s + pathEps N (f 0) Q := by
          simp [augment]
        exact Real.logb_nonneg hb1 (by linarith)
      · have hno : ∀ Q : List V, IsAugPath N (f 0) Q → pathEps N (f 0) Q ≤ 0 :=
          fun Q hQ => absurd ⟨Q, hQ⟩ hex
        have h1 := aux_mab_noaug_bound N M hcross (f 0) hf0 0 le_rfl hno g hg.1
        have h2 := hg.2 _ hf0
        obtain ⟨z, hz⟩ := hint _ (aux_mab_ts_mem_arcs N)
        have hgz : g N.t N.s = z := by simp only at hz; linarith
        rw [hgz]
        have hz0 : (0 : ℝ) ≤ z := by simp only at hz; linarith
        have hz0' : (0 : ℤ) ≤ z := by exact_mod_cast hz0
        rcases eq_or_lt_of_le hz0' with hz1 | hz1
        · rw [← hz1]; simp
        · have : (1 : ℤ) ≤ z := hz1
          exact Real.logb_nonneg hb1 (by exact_mod_cast this)
    · obtain ⟨n, rfl⟩ : ∃ n, K = n + 1 := ⟨K - 1, by omega⟩
      have hv := hval n (by omega)
      have he := hε1 n (by omega)
      have hgK := hg.2 _ (hFI (n + 1) le_rfl).1
      have hrn := hr n (by omega)
      have hqn : 0 ≤ q ^ n := pow_nonneg hq0 n
      have h1 : 1 ≤ q ^ n * g N.t N.s := by
        have : q ^ n * (g N.t N.s - f 0 N.t N.s) ≤ q ^ n * g N.t N.s :=
          mul_le_mul_of_nonneg_left (by linarith) hqn
        linarith
      have hgpos : 0 < g N.t N.s := by
        by_contra hneg
        rw [not_lt] at hneg
        have : q ^ n * g N.t N.s ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hqn hneg
        linarith
      have hbq : (M : ℝ) / ((M : ℝ) - 1) * q = 1 := by
        rw [hq]
        have : (M : ℝ) - 1 ≠ 0 := by linarith
        field_simp
      have hbn : ((M : ℝ) / ((M : ℝ) - 1)) ^ n ≤ g N.t N.s := by
        have hbpos : 0 ≤ ((M : ℝ) / ((M : ℝ) - 1)) ^ n := pow_nonneg (by linarith) n
        calc ((M : ℝ) / ((M : ℝ) - 1)) ^ n = ((M : ℝ) / ((M : ℝ) - 1)) ^ n * 1 := by ring
          _ ≤ ((M : ℝ) / ((M : ℝ) - 1)) ^ n * (q ^ n * g N.t N.s) :=
            mul_le_mul_of_nonneg_left h1 hbpos
          _ = ((M : ℝ) / ((M : ℝ) - 1) * q) ^ n * g N.t N.s := by rw [mul_pow, mul_assoc]
          _ = g N.t N.s := by rw [hbq]; ring
      have hlog : (n : ℝ) ≤ Real.logb ((M : ℝ) / ((M : ℝ) - 1)) (g N.t N.s) := by
        rw [Real.le_logb_iff_rpow_le hb1 hgpos, Real.rpow_natCast]
        exact hbn
      push_cast
      linarith
  · intro hno
    refine ⟨(hFI K le_rfl).1, fun h hh => ?_⟩
    have hno' : ∀ Q : List V, IsAugPath N (f K) Q → pathEps N (f K) Q ≤ 0 :=
      fun Q hQ => absurd ⟨Q, hQ⟩ hno
    have := aux_mab_noaug_bound N M hcross (f K) (hFI K le_rfl).1 0 le_rfl hno' h hh
    linarith
