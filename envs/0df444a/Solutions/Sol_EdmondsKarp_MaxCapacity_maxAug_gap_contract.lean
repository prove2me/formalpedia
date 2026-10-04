-- Prove2me | solution 1 for EdmondsKarp.MaxCapacity.maxAug_gap_contract
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T12:30:11.123994+00:00
-- url     : https://prove2.me/submissions/c604010a-cc72-4362-9c31-5aab068d0f2d

import Mathlib
import Definitions.Def_EdmondsKarp_MaxCapacity_Network
import Definitions.Def_EdmondsKarp_MaxCapacity_Augmentation
import Definitions.Def_EdmondsKarp_MaxCapacity_Run

set_option autoImplicit false

namespace EdmondsKarp.MaxCapacity.B845

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

lemma run_flow {N : Network V} {K : ℕ} {f : ℕ → V → V → ℝ} {P : ℕ → List V}
    (hrun : IsMaxAugRun N K f P) : ∀ k, k ≤ K → IsFlow N (f k) := by
  intro k
  induction k with
  | zero => intro _; exact hrun.1
  | succ k ih =>
    intro hk
    have hk' : k < K := hk
    obtain ⟨hP, hf⟩ := hrun.2 k hk'
    rw [hf]
    exact aug_flow (ih (le_of_lt hk')) hP.1

/-! ### Cut identity -/

lemma sum_to_univ (A : Finset (V × V)) (H : V × V → ℝ) :
    ∑ p ∈ A, H p = ∑ p : V × V, if p ∈ A then H p else 0 := by
  rw [← Finset.sum_filter]; congr 1; ext p; simp

lemma sum_prod_ind (S T : Finset V) (F : V → V → ℝ) :
    ∑ u ∈ S, ∑ v ∈ T, F u v = ∑ p : V × V, if p.1 ∈ S ∧ p.2 ∈ T then F p.1 p.2 else 0 := by
  rw [← Finset.sum_product', ← Finset.sum_filter]
  congr 1; ext p; simp [Finset.mem_product]

lemma flow_cut {N : Network V} {f : V → V → ℝ} (hf : IsFlow N f) (X : Finset V)
    (hs : N.s ∈ X) (ht : N.t ∉ X) : f N.t N.s = cutFlowOut N f X - cutFlowIn N f X := by
  have h0 : ∑ u ∈ X, ((∑ v ∈ Finset.univ.filter (fun v => (u, v) ∈ N.arcs), f u v) -
      (∑ v ∈ Finset.univ.filter (fun v => (v, u) ∈ N.arcs), f v u)) = 0 := by
    apply Finset.sum_eq_zero; intro u _; exact hf.2.2 u
  simp only [Finset.sum_filter] at h0
  rw [Finset.sum_sub_distrib] at h0
  rw [Finset.sum_comm (s := X) (t := Finset.univ)
    (f := fun u v => if (v, u) ∈ N.arcs then f v u else 0)] at h0
  rw [sum_prod_ind X Finset.univ (fun u v => if (u, v) ∈ N.arcs then f u v else 0),
    sum_prod_ind Finset.univ X (fun u v => if (u, v) ∈ N.arcs then f u v else 0)] at h0
  have eo : cutFlowOut N f X
      = ∑ p : V × V, if p ∈ N.A then (if p.1 ∈ X ∧ p.2 ∉ X then f p.1 p.2 else 0) else 0 := by
    unfold cutFlowOut; rw [Finset.sum_filter]; exact sum_to_univ _ _
  have ei : cutFlowIn N f X
      = ∑ p : V × V, if p ∈ N.A then (if p.1 ∉ X ∧ p.2 ∈ X then f p.1 p.2 else 0) else 0 := by
    unfold cutFlowIn; rw [Finset.sum_filter]; exact sum_to_univ _ _
  have hts : f N.t N.s = ∑ p : V × V, if p = (N.t, N.s) then f p.1 p.2 else 0 := by simp
  have key : ∀ p : V × V,
      ((if p.1 ∈ X ∧ p.2 ∈ Finset.univ then (if (p.1, p.2) ∈ N.arcs then f p.1 p.2 else 0) else 0)
        - (if p.1 ∈ Finset.univ ∧ p.2 ∈ X then (if (p.1, p.2) ∈ N.arcs then f p.1 p.2 else 0) else 0))
      = (if p ∈ N.A then (if p.1 ∈ X ∧ p.2 ∉ X then f p.1 p.2 else 0) else 0)
        - (if p ∈ N.A then (if p.1 ∉ X ∧ p.2 ∈ X then f p.1 p.2 else 0) else 0)
        - (if p = (N.t, N.s) then f p.1 p.2 else 0) := by
    rintro ⟨a, b⟩
    by_cases hab : a = N.t ∧ b = N.s
    · obtain ⟨rfl, rfl⟩ := hab
      simp [Network.arcs, hs, ht, N.return_not_mem]
    · have hne : (a, b) ≠ (N.t, N.s) := by
        intro h; simp only [Prod.mk.injEq] at h; exact hab h
      have harc : (a, b) ∈ N.arcs ↔ (a, b) ∈ N.A := by
        unfold Network.arcs; rw [Finset.mem_insert]; simp [hne]
      simp only [harc, if_neg hne]
      by_cases hA : (a, b) ∈ N.A <;> by_cases ha : a ∈ X <;> by_cases hb : b ∈ X <;>
        simp [hA, ha, hb]
  have hsum := Finset.sum_congr (s₁ := (Finset.univ : Finset (V × V))) rfl (fun p _ => key p)
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib] at hsum
  rw [eo, ei]
  linarith

/-! ### The main bound -/

lemma gap_le {N : Network V} {M : ℕ} (hcross : CrossArcsBounded N M) {f g : V → V → ℝ}
    (hf : IsFlow N f) (hg : IsFlow N g) {P : List V} (hP : IsMaxAugPath N f P) :
    g N.t N.s - f N.t N.s ≤ (M : ℝ) * pathEps N f P := by
  classical
  set ε := pathEps N f P with hεdef
  have hε0 : 0 ≤ ε := pathEps_nonneg hf hP.1
  let good : V → V → Prop := fun u v => ResArc N f u v ∧ ε < stepEps N f u v
  let GP : V → Prop := fun u => ∃ L : List V, L.Nodup ∧ L.head? = some u ∧
    L.getLast? = some N.t ∧ ∀ e ∈ pathArcs L, good e.1 e.2
  have closure : ∀ u v, good u v → GP v → GP u := by
    rintro u v hgood ⟨L, hnd, hh, hl, hgd⟩
    by_cases hu : u ∈ L
    · obtain ⟨L1, L2, rfl⟩ := List.append_of_mem hu
      refine ⟨u :: L2, hnd.sublist (List.sublist_append_right L1 (u :: L2)), rfl, ?_, ?_⟩
      · rw [← hl, List.getLast?_append, List.getLast?_cons]; rfl
      · intro e he; exact hgd e (pathArcs_sub_append L1 (u :: L2) e he)
    · cases L with
      | nil => simp at hh
      | cons a R =>
        have ha : a = v := by simpa using hh
        subst ha
        refine ⟨u :: a :: R, List.nodup_cons.mpr ⟨hu, hnd⟩, rfl, ?_, ?_⟩
        · rw [← hl]; simp [List.getLast?_cons_cons]
        · rw [pathArcs_cons_cons]
          intro e he
          rcases List.mem_cons.mp he with he | he
          · subst he; exact hgood
          · exact hgd e he
  let X : Finset V := Finset.univ.filter (fun u => ¬ GP u)
  have hsX : N.s ∈ X := by
    simp only [X, Finset.mem_filter, Finset.mem_univ, true_and]
    rintro ⟨L, hnd, hh, hl, hgd⟩
    have haug : IsAugPath N f L := ⟨hnd, hh, hl, fun e he => (hgd e he).1⟩
    have h1 := hP.2 L haug
    have h2 := pathEps_gt (pathArcs_ne_nil hh hl) (fun e he => (hgd e he).2)
    linarith
  have htX : N.t ∉ X := by
    simp only [X, Finset.mem_filter, Finset.mem_univ, true_and, not_not]
    exact ⟨[N.t], List.nodup_singleton _, rfl, rfl, by simp [pathArcs_single]⟩
  have hcr : ∀ u v, u ∈ X → v ∉ X → ¬ good u v := by
    intro u v hu hv hgood
    simp only [X, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hu hv
    exact hu (closure u v hgood hv)
  have hout : ∀ p ∈ N.A.filter (fun p => p.1 ∈ X ∧ p.2 ∉ X), N.c p.1 p.2 - f p.1 p.2 ≤ ε := by
    rintro ⟨u, v⟩ hp
    simp only [Finset.mem_filter] at hp
    obtain ⟨hA, hu, hv⟩ := hp
    have hng := hcr u v hu hv
    simp only [good, not_and, not_lt] at hng
    by_cases hr : ResArc N f u v
    · have h1 := hng hr
      unfold stepEps at h1
      rw [if_pos hA] at h1
      split_ifs at h1 with hB
      · have := hf.1 v u (arc_of_A N hB); simp only; linarith
      · simp only; linarith
    · unfold ResArc at hr; push_neg at hr
      have := hr.1 hA; simp only; linarith
  have hin : ∀ p ∈ N.A.filter (fun p => p.1 ∉ X ∧ p.2 ∈ X), f p.1 p.2 ≤ ε := by
    rintro ⟨v, u⟩ hp
    simp only [Finset.mem_filter] at hp
    obtain ⟨hA, hv, hu⟩ := hp
    have hng := hcr u v hu hv
    simp only [good, not_and, not_lt] at hng
    by_cases hr : ResArc N f u v
    · have h1 := hng hr
      unfold stepEps at h1
      split_ifs at h1 with hB
      · have := hf.2.1 u v hB; simp only; linarith
      · simp only; linarith
    · unfold ResArc at hr; push_neg at hr
      have := hr.2 hA; simp only; linarith
  have cf := flow_cut hf X hsX htX
  have cg := flow_cut hg X hsX htX
  rw [cf, cg]
  unfold cutFlowOut cutFlowIn
  set Sout := N.A.filter (fun p => p.1 ∈ X ∧ p.2 ∉ X) with hSout
  set Sin := N.A.filter (fun p => p.1 ∉ X ∧ p.2 ∈ X) with hSin
  have b1 : ∑ p ∈ Sout, g p.1 p.2 - ∑ p ∈ Sout, f p.1 p.2 ≤ Sout.card * ε := by
    rw [← Finset.sum_sub_distrib]
    have : ∑ p ∈ Sout, (g p.1 p.2 - f p.1 p.2) ≤ ∑ p ∈ Sout, ε := by
      apply Finset.sum_le_sum
      intro p hp
      have h1 := hout p hp
      have hpA : p ∈ N.A := (Finset.mem_filter.mp hp).1
      have h2 := hg.2.1 p.1 p.2 hpA
      linarith
    simpa using this
  have b2 : ∑ p ∈ Sin, f p.1 p.2 - ∑ p ∈ Sin, g p.1 p.2 ≤ Sin.card * ε := by
    rw [← Finset.sum_sub_distrib]
    have : ∑ p ∈ Sin, (f p.1 p.2 - g p.1 p.2) ≤ ∑ p ∈ Sin, ε := by
      apply Finset.sum_le_sum
      intro p hp
      have h1 := hin p hp
      have hpA : p ∈ N.A := (Finset.mem_filter.mp hp).1
      have h2 := hg.1 p.1 p.2 (arc_of_A N hpA)
      linarith
    simpa using this
  have hcard : Sout.card + Sin.card ≤ M := by
    have hdisj : Disjoint Sout Sin := by
      rw [Finset.disjoint_left]
      intro p h1 h2
      simp only [hSout, hSin, Finset.mem_filter] at h1 h2
      exact h2.2.1 h1.2.1
    rw [← Finset.card_union_of_disjoint hdisj]
    refine le_trans ?_ (hcross X hsX htX)
    unfold crossArcCount
    apply Finset.card_le_card
    intro p hp
    rcases Finset.mem_union.mp hp with h | h
    · simp only [hSout, Finset.mem_filter] at h
      exact Finset.mem_filter.mpr ⟨arc_of_A N h.1, Or.inl h.2⟩
    · simp only [hSin, Finset.mem_filter] at h
      exact Finset.mem_filter.mpr ⟨arc_of_A N h.1, Or.inr h.2⟩
  have hcardR : (Sout.card : ℝ) + Sin.card ≤ M := by exact_mod_cast hcard
  nlinarith

end EdmondsKarp.MaxCapacity.B845

open EdmondsKarp.MaxCapacity in
theorem solution {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (hcap : IntegralCaps N) (M : ℕ) (hM : 1 < M) (hcross : CrossArcsBounded N M)
    (g : V → V → ℝ) (hg : IsMaxFlow N g)
    (K : ℕ) (f : ℕ → V → V → ℝ) (P : ℕ → List V) (hrun : IsMaxAugRun N K f P)
    (k : ℕ) (hk : k < K) :
    g N.t N.s - f (k + 1) N.t N.s ≤ (g N.t N.s - f k N.t N.s) * (1 - (M : ℝ)⁻¹) := by
  have hfk := EdmondsKarp.MaxCapacity.B845.run_flow hrun k (le_of_lt hk)
  obtain ⟨hPk, hstep⟩ := hrun.2 k hk
  have hgap := EdmondsKarp.MaxCapacity.B845.gap_le hcross hfk hg.1 hPk
  have hnext : f (k + 1) N.t N.s = f k N.t N.s + pathEps N (f k) (P k) := by
    rw [hstep]; exact EdmondsKarp.MaxCapacity.B845.aug_ts
  rw [hnext]
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (lt_trans Nat.zero_lt_one hM)
  set ε := pathEps N (f k) (P k)
  set G := g N.t N.s - f k N.t N.s
  have h1 : G * (M : ℝ)⁻¹ ≤ ε := by
    rw [mul_inv_le_iff₀ hMpos]; linarith
  have : G * (1 - (M : ℝ)⁻¹) = G - G * (M : ℝ)⁻¹ := by ring
  rw [this]; linarith
