-- Prove2me | solution 1 for EdmondsKarp.MaxCapacity.augment_isFlow
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T06:20:58.38318+00:00
-- url     : https://prove2.me/submissions/858abf2e-1245-4750-8b6b-6356055402ba

import Mathlib
import Definitions.Def_EdmondsKarp_MaxCapacity_Network
import Definitions.Def_EdmondsKarp_MaxCapacity_Augmentation

set_option autoImplicit false

namespace EdmondsKarp.MaxCapacity.BAD08

open EdmondsKarp.MaxCapacity

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### List / path facts -/

lemma pathArcs_cons_cons (a b : V) (R : List V) :
    pathArcs (a :: b :: R) = (a, b) :: pathArcs (b :: R) := by
  simp [pathArcs]

lemma pathArcs_single (a : V) : pathArcs [a] = [] := by simp [pathArcs]

lemma mem_of_mem_pathArcs {L : List V} {x y : V} (h : (x, y) ∈ pathArcs L) :
    x ∈ L ∧ y ∈ L := by
  unfold pathArcs at h
  have := List.of_mem_zip h
  exact ⟨this.1, List.mem_of_mem_tail this.2⟩

lemma pathArcs_sub_cons (a : V) (L : List V) : ∀ e ∈ pathArcs L, e ∈ pathArcs (a :: L) := by
  intro e he
  cases L with
  | nil => simp [pathArcs] at he
  | cons b R => rw [pathArcs_cons_cons]; exact List.mem_cons_of_mem _ he

lemma pathArcs_sub_append (L1 M : List V) : ∀ e ∈ pathArcs M, e ∈ pathArcs (L1 ++ M) := by
  induction L1 with
  | nil => simp
  | cons a L1 ih => intro e he; exact pathArcs_sub_cons a (L1 ++ M) e (ih e he)

lemma not_both_pathArcs : ∀ (L : List V), L.Nodup → ∀ (u v : V),
    (u, v) ∈ pathArcs L → (v, u) ∈ pathArcs L → False
  | [], _, _, _, h, _ => by simp [pathArcs] at h
  | [a], _, _, _, h, _ => by simp [pathArcs] at h
  | a :: b :: R, hnd, u, v, h1, h2 => by
    rw [pathArcs_cons_cons] at h1 h2
    have hnd' : (b :: R).Nodup := hnd.of_cons
    have ha : a ∉ b :: R := (List.nodup_cons.mp hnd).1
    rcases List.mem_cons.mp h1 with k1 | k1 <;> rcases List.mem_cons.mp h2 with k2 | k2
    · simp only [Prod.mk.injEq] at k1 k2
      exact ha (by rw [← k1.1, k2.2]; exact List.mem_cons_self)
    · simp only [Prod.mk.injEq] at k1
      have := (mem_of_mem_pathArcs k2).2
      rw [k1.1] at this
      exact ha this
    · simp only [Prod.mk.injEq] at k2
      have := (mem_of_mem_pathArcs k1).2
      rw [k2.1] at this
      exact ha this
    · exact not_both_pathArcs (b :: R) hnd' u v k1 k2

lemma sum_ind_left (u x y : V) (c : ℝ) :
    (∑ v : V, (if (u, v) = (x, y) then c else 0)) = if u = x then c else 0 := by
  by_cases hu : u = x
  · subst hu; simp
  · simp [hu]

lemma sum_ind_right (u x y : V) (c : ℝ) :
    (∑ v : V, (if (v, u) = (x, y) then c else 0)) = if u = y then c else 0 := by
  by_cases hu : u = y
  · subst hu; simp
  · simp [hu]

lemma deg_pathArcs : ∀ (L : List V), L.Nodup → ∀ (a b : V), L.head? = some a →
    L.getLast? = some b → ∀ u : V,
    (∑ v, (if (u, v) ∈ pathArcs L then (1:ℝ) else 0)) -
      (∑ v, (if (v, u) ∈ pathArcs L then (1:ℝ) else 0))
      = (if u = a then 1 else 0) - (if u = b then 1 else 0)
  | [], _, a, b, h, _, u => by simp at h
  | [x], _, a, b, h1, h2, u => by
      simp at h1 h2; subst h1; subst h2; simp [pathArcs]
  | x :: y :: R, hnd, a, b, h1, h2, u => by
      have hx : x = a := by simpa using h1
      subst hx
      have hnd' : (y :: R).Nodup := hnd.of_cons
      have hxn : x ∉ y :: R := (List.nodup_cons.mp hnd).1
      have h2' : (y :: R).getLast? = some b := by
        rw [← h2]; simp [List.getLast?_cons_cons]
      have ih := deg_pathArcs (y :: R) hnd' y b rfl h2' u
      rw [pathArcs_cons_cons]
      have e1 : ∀ v, (if (u, v) ∈ (x, y) :: pathArcs (y :: R) then (1:ℝ) else 0)
          = (if (u, v) = (x, y) then 1 else 0) + (if (u, v) ∈ pathArcs (y :: R) then 1 else 0) := by
        intro v
        by_cases h : (u, v) = (x, y)
        · have hn : (u, v) ∉ pathArcs (y :: R) := by
            intro hm; rw [h] at hm; exact hxn (mem_of_mem_pathArcs hm).1
          rw [if_pos (List.mem_cons.mpr (Or.inl h)), if_pos h, if_neg hn]; norm_num
        · rw [if_neg h]; simp only [List.mem_cons, h, false_or, zero_add]
      have e2 : ∀ v, (if (v, u) ∈ (x, y) :: pathArcs (y :: R) then (1:ℝ) else 0)
          = (if (v, u) = (x, y) then 1 else 0) + (if (v, u) ∈ pathArcs (y :: R) then 1 else 0) := by
        intro v
        by_cases h : (v, u) = (x, y)
        · have hn : (v, u) ∉ pathArcs (y :: R) := by
            intro hm; rw [h] at hm; exact hxn (mem_of_mem_pathArcs hm).1
          rw [if_pos (List.mem_cons.mpr (Or.inl h)), if_pos h, if_neg hn]; norm_num
        · rw [if_neg h]; simp only [List.mem_cons, h, false_or, zero_add]
      simp only [e1, e2, Finset.sum_add_distrib, sum_ind_left, sum_ind_right]
      linarith

/-! ### Step values -/

lemma arc_of_A (N : Network V) {p : V × V} (h : p ∈ N.A) : p ∈ N.arcs := by
  unfold Network.arcs; exact Finset.mem_insert_of_mem h

lemma stepEps_pos {N : Network V} {f : V → V → ℝ} (hf : IsFlow N f) {u v : V}
    (hr : ResArc N f u v) : 0 < stepEps N f u v := by
  unfold stepEps
  rcases hr with ⟨hA, hpos⟩ | ⟨hA, hpos⟩
  · rw [if_pos hA]
    split_ifs with hB
    · have := hf.1 v u (arc_of_A N hB); linarith
    · exact hpos
  · split_ifs with h1
    · have := hf.2.1 u v h1; linarith
    · exact hpos

lemma pathEps_le {N : Network V} {f : V → V → ℝ} {P : List V} {e : V × V}
    (he : e ∈ pathArcs P) : pathEps N f P ≤ stepEps N f e.1 e.2 := by
  unfold pathEps
  set l := (pathArcs P).map (fun e => stepEps N f e.1 e.2) with hl
  have hmem : stepEps N f e.1 e.2 ∈ l := List.mem_map.mpr ⟨e, he, rfl⟩
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp (List.isSome_min?_of_mem hmem)
  rw [hm]
  exact ((List.min?_eq_some_iff.mp hm).2 _ hmem)

lemma pathEps_nonneg {N : Network V} {f : V → V → ℝ} (hf : IsFlow N f) {P : List V}
    (hP : IsAugPath N f P) : 0 ≤ pathEps N f P := by
  unfold pathEps
  cases hm : ((pathArcs P).map (fun e => stepEps N f e.1 e.2)).min? with
  | none => simp
  | some m =>
    have hmem := List.min?_mem hm
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hmem
    exact le_of_lt (stepEps_pos hf (hP.2.2.2 e he))

lemma pathEps_gt {N : Network V} {f : V → V → ℝ} {P : List V} {ε : ℝ}
    (hne : pathArcs P ≠ []) (h : ∀ e ∈ pathArcs P, ε < stepEps N f e.1 e.2) :
    ε < pathEps N f P := by
  unfold pathEps
  have hne' : (pathArcs P).map (fun e => stepEps N f e.1 e.2) ≠ [] := by simpa using hne
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp (List.isSome_min?_of_ne_nil hne')
  rw [hm]
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp (List.min?_mem hm)
  exact h e he

lemma pathArcs_ne_nil {N : Network V} {P : List V} (hh : P.head? = some N.s)
    (hl : P.getLast? = some N.t) : pathArcs P ≠ [] := by
  match P, hh, hl with
  | [], hh, _ => simp at hh
  | [a], hh, hl =>
    simp at hh hl
    exact absurd (hh.symm.trans hl) N.source_ne_sink
  | a :: b :: R, _, _ => rw [pathArcs_cons_cons]; simp

/-! ### Augmentation preserves flows -/

lemma min_max_aux (e r : ℝ) : min e r + max 0 (e - r) = e := by
  rcases le_total e r with h | h
  · rw [min_eq_left h, max_eq_left (by linarith)]; ring
  · rw [min_eq_right h, max_eq_right (by linarith)]; ring

lemma aug_A {N : Network V} {f : V → V → ℝ} {P : List V} {x y : V} (hxy : (x, y) ∈ N.A) :
    augment N f P x y = f x y + augIncrease N f P x y - augDecrease N f P x y := by
  unfold augment
  rw [if_neg, if_pos hxy]
  rintro ⟨rfl, rfl⟩
  exact N.return_not_mem hxy

lemma aug_ts {N : Network V} {f : V → V → ℝ} {P : List V} :
    augment N f P N.t N.s = f N.t N.s + pathEps N f P := by
  unfold augment; simp

lemma aug_bounds {N : Network V} {f : V → V → ℝ} (hf : IsFlow N f) {P : List V}
    (hP : IsAugPath N f P) {x y : V} (hxy : (x, y) ∈ N.A) :
    0 ≤ augment N f P x y ∧ augment N f P x y ≤ N.c x y := by
  rw [aug_A hxy]
  have hε := pathEps_nonneg hf hP
  have hf0 := hf.1 x y (arc_of_A N hxy)
  have hfc := hf.2.1 x y hxy
  set ε := pathEps N f P with hεdef
  by_cases h1 : (x, y) ∈ pathArcs P
  · have h2 : (y, x) ∉ pathArcs P := fun h2 => not_both_pathArcs P hP.1 x y h1 h2
    have hle := pathEps_le (N := N) (f := f) h1
    simp only at hle
    unfold augIncrease augDecrease
    rw [if_pos h1, if_neg h2]
    by_cases hyx : (y, x) ∈ N.A
    · rw [if_pos hyx]
      have : 0 ≤ min ε (N.c x y - f x y) := le_min hε (by linarith)
      have : min ε (N.c x y - f x y) ≤ N.c x y - f x y := min_le_right _ _
      constructor <;> linarith
    · rw [if_neg hyx]
      unfold stepEps at hle
      rw [if_pos hxy, if_neg hyx] at hle
      constructor <;> linarith
  · by_cases h2 : (y, x) ∈ pathArcs P
    · have hle := pathEps_le (N := N) (f := f) h2
      simp only at hle
      unfold augIncrease augDecrease
      rw [if_neg h1, if_pos h2]
      unfold stepEps at hle
      by_cases hyx : (y, x) ∈ N.A
      · rw [if_pos hyx]
        rw [if_pos hyx, if_pos hxy] at hle
        have : max 0 (ε - N.c y x + f y x) ≤ f x y := max_le hf0 (by linarith)
        have : 0 ≤ max 0 (ε - N.c y x + f y x) := le_max_left _ _
        constructor <;> linarith
      · rw [if_neg hyx]
        rw [if_neg hyx] at hle
        constructor <;> linarith
    · unfold augIncrease augDecrease
      rw [if_neg h1, if_neg h2]
      constructor <;> linarith

lemma arcDelta {N : Network V} {f : V → V → ℝ} {P : List V} (x y : V) :
    (if (x, y) ∈ N.arcs then augment N f P x y - f x y else 0)
      = (if (x, y) = (N.t, N.s) then pathEps N f P else 0)
        + (if (x, y) ∈ N.A then augIncrease N f P x y - augDecrease N f P x y else 0) := by
  by_cases h1 : (x, y) = (N.t, N.s)
  · have hA : (x, y) ∉ N.A := by rw [h1]; exact N.return_not_mem
    have harc : (x, y) ∈ N.arcs := by rw [h1]; unfold Network.arcs; exact Finset.mem_insert_self _ _
    simp only [Prod.mk.injEq] at h1
    obtain ⟨hx, hy⟩ := h1
    rw [if_pos harc, if_pos (by rw [hx, hy]), if_neg hA, hx, hy, aug_ts]; ring
  · by_cases h2 : (x, y) ∈ N.A
    · rw [if_pos (arc_of_A N h2), if_neg h1, if_pos h2, aug_A h2]; ring
    · have : (x, y) ∉ N.arcs := by
        unfold Network.arcs; rw [Finset.mem_insert]; push_neg; exact ⟨h1, h2⟩
      rw [if_neg this, if_neg h1, if_neg h2]; ring

lemma pairDelta {N : Network V} {f : V → V → ℝ} {P : List V} (hP : IsAugPath N f P) (u v : V) :
    (if (u, v) ∈ N.A then augIncrease N f P u v - augDecrease N f P u v else 0)
      - (if (v, u) ∈ N.A then augIncrease N f P v u - augDecrease N f P v u else 0)
      = pathEps N f P * ((if (u, v) ∈ pathArcs P then 1 else 0)
          - (if (v, u) ∈ pathArcs P then 1 else 0)) := by
  set ε := pathEps N f P with hεdef
  unfold augIncrease augDecrease
  rw [← hεdef]
  by_cases h1 : (u, v) ∈ pathArcs P
  · have h2 : (v, u) ∉ pathArcs P := fun h2 => not_both_pathArcs P hP.1 u v h1 h2
    have hres : ResArc N f u v := hP.2.2.2 (u, v) h1
    simp only [if_pos h1, if_neg h2]
    by_cases hA : (u, v) ∈ N.A <;> by_cases hB : (v, u) ∈ N.A
    · simp only [if_pos hA, if_pos hB]
      have := min_max_aux ε (N.c u v - f u v)
      have e : ε - N.c u v + f u v = ε - (N.c u v - f u v) := by ring
      rw [e]; linarith
    · simp only [if_pos hA, if_neg hB]; ring
    · simp only [if_neg hA, if_pos hB]; ring
    · exfalso; rcases hres with ⟨h, _⟩ | ⟨h, _⟩
      · exact hA h
      · exact hB h
  · by_cases h2 : (v, u) ∈ pathArcs P
    · have hres : ResArc N f v u := hP.2.2.2 (v, u) h2
      simp only [if_pos h2, if_neg h1]
      by_cases hA : (u, v) ∈ N.A <;> by_cases hB : (v, u) ∈ N.A
      · simp only [if_pos hA, if_pos hB]
        have := min_max_aux ε (N.c v u - f v u)
        have e : ε - N.c v u + f v u = ε - (N.c v u - f v u) := by ring
        rw [e]; linarith
      · simp only [if_pos hA, if_neg hB]; ring
      · simp only [if_neg hA, if_pos hB]; ring
      · exfalso; rcases hres with ⟨h, _⟩ | ⟨h, _⟩
        · exact hB h
        · exact hA h
    · simp only [if_neg h1, if_neg h2]; split_ifs <;> ring

lemma aug_flow {N : Network V} {f : V → V → ℝ} (hf : IsFlow N f) {P : List V}
    (hP : IsAugPath N f P) : IsFlow N (augment N f P) := by
  have hε := pathEps_nonneg hf hP
  refine ⟨?_, ?_, ?_⟩
  · intro u v huv
    unfold Network.arcs at huv
    rcases Finset.mem_insert.mp huv with h | h
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [aug_ts]; have := hf.1 N.t N.s (by unfold Network.arcs; exact Finset.mem_insert_self _ _)
      linarith
    · exact (aug_bounds hf hP h).1
  · intro u v huv; exact (aug_bounds hf hP huv).2
  · intro u
    have h0 := hf.2.2 u
    simp only [Finset.sum_filter] at h0 ⊢
    have key : ∀ v, (if (u, v) ∈ N.arcs then augment N f P u v else 0)
        - (if (v, u) ∈ N.arcs then augment N f P v u else 0)
        = ((if (u, v) ∈ N.arcs then f u v else 0) - (if (v, u) ∈ N.arcs then f v u else 0))
          + ((if (u, v) = (N.t, N.s) then pathEps N f P else 0)
             - (if (v, u) = (N.t, N.s) then pathEps N f P else 0))
          + pathEps N f P * ((if (u, v) ∈ pathArcs P then 1 else 0)
              - (if (v, u) ∈ pathArcs P then 1 else 0)) := by
      intro v
      have a1 := arcDelta (N := N) (f := f) (P := P) u v
      have a2 := arcDelta (N := N) (f := f) (P := P) v u
      have a3 := pairDelta hP u v
      have b1 : (if (u, v) ∈ N.arcs then augment N f P u v else 0)
          = (if (u, v) ∈ N.arcs then f u v else 0)
            + (if (u, v) ∈ N.arcs then augment N f P u v - f u v else 0) := by
        split_ifs <;> ring
      have b2 : (if (v, u) ∈ N.arcs then augment N f P v u else 0)
          = (if (v, u) ∈ N.arcs then f v u else 0)
            + (if (v, u) ∈ N.arcs then augment N f P v u - f v u else 0) := by
        split_ifs <;> ring
      rw [b1, b2, a1, a2]; linarith
    rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl (fun v _ => key v),
      Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, sum_ind_left,
      sum_ind_right, deg_pathArcs P hP.1 N.s N.t hP.2.1 hP.2.2.1 u, h0]
    split_ifs <;> ring

lemma pathEps_pos {N : Network V} {f : V → V → ℝ} (hf : IsFlow N f) {P : List V}
    (hP : IsAugPath N f P) : 0 < pathEps N f P :=
  pathEps_gt (pathArcs_ne_nil hP.2.1 hP.2.2.1) (fun e he => stepEps_pos hf (hP.2.2.2 e he))

end EdmondsKarp.MaxCapacity.BAD08

open EdmondsKarp.MaxCapacity in
theorem solution {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (f : V → V → ℝ) (P : List V) (hf : IsFlow N f) (hP : IsAugPath N f P) :
    IsFlow N (augment N f P) ∧ 0 < pathEps N f P ∧
      augment N f P N.t N.s = f N.t N.s + pathEps N f P := by
  exact ⟨EdmondsKarp.MaxCapacity.BAD08.aug_flow hf hP, EdmondsKarp.MaxCapacity.BAD08.pathEps_pos hf hP,
    EdmondsKarp.MaxCapacity.BAD08.aug_ts⟩
