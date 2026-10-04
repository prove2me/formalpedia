-- Prove2me | solution 1 for DiscreteConvex.CombinatorialC.prop_2_24_circuit_parallel_series_support
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T17:41:38.704491+00:00
-- url     : https://prove2.me/submissions/712ec4dd-1be8-4398-b868-3ad3dea1b139

import Mathlib
import Definitions.Def_DiscreteConvex_CombinatorialC_IsCircuit
import Definitions.Def_DiscreteConvex_CombinatorialC_IsParallelArcSet
import Definitions.Def_DiscreteConvex_CombinatorialC_IsSeriesArcSet
import Definitions.Def_DiscreteConvex_CombinatorialC_SuppPosR
import Definitions.Def_DiscreteConvex_CombinatorialC_SuppNegR

open DiscreteConvex.CombinatorialC

namespace CircuitSupportCore

variable {V A : Type*} [Fintype A] [Fintype V] [DecidableEq V] [DecidableEq A]

/-- Orientation sign of the `i`-th arc of a cycle traversal. -/
noncomputable def orient (src : A → V) {k : ℕ} (v : Fin (k + 1) → V) (arcs : Fin (k + 1) → A)
    (i : Fin (k + 1)) : ℝ := by
  classical
  exact if Forward src v arcs i then 1 else -1

/-- Incidence sign of an arc at a vertex. -/
noncomputable def inc (src dst : A → V) (w : V) (a : A) : ℝ :=
  (if src a = w then 1 else 0) - (if dst a = w then 1 else 0)

lemma boundary_eq (src dst : A → V) (pi : A → ℝ) (w : V) :
    Boundary src dst pi w = ∑ a, pi a * inc src dst w a := by
  unfold Boundary inc
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  split_ifs <;> ring

/-- `{s, d} = {x, y}` as finsets, with `s = x` excluded, forces `s = y` and `d = x`. -/
lemma ends_of_not {s d x y : V} (h : ({s, d} : Finset V) = {x, y}) (hxy : x ≠ y) :
    (s = x ∧ d = y) ∨ (s = y ∧ d = x) := by
  have hs : s ∈ ({x, y} : Finset V) := h ▸ (by simp)
  have hd : d ∈ ({x, y} : Finset V) := h ▸ (by simp)
  have hx : x ∈ ({s, d} : Finset V) := h.symm ▸ (by simp)
  have hy : y ∈ ({s, d} : Finset V) := h.symm ▸ (by simp)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs hd hx hy
  rcases hs with rfl | rfl <;> rcases hd with rfl | rfl
  · rcases hy with h1 | h1 <;> exact absurd h1.symm hxy
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · rcases hx with h1 | h1 <;> exact absurd h1 hxy

end CircuitSupportCore

open CircuitSupportCore in
theorem solution {V A : Type*} [Fintype A] [Fintype V]
    [DecidableEq V] [DecidableEq A] (src dst : A → V) (pi : A → ℝ)
    (hpi : IsCircuit src dst pi) (P S : Finset A) (hP : IsParallelArcSet src dst P)
    (hS : IsSeriesArcSet src dst S) :
    ((SuppPosR pi ∩ P).card ≤ 1 ∧ (SuppNegR pi ∩ P).card ≤ 1) ∧
      ((SuppPosR pi ∩ S) = ∅ ∨ (SuppNegR pi ∩ S) = ∅) := by
  obtain ⟨hval, hbd, k, v, arcs, ⟨hinj, hends⟩, himg⟩ := hpi
  set T : Finset A := Finset.image arcs Finset.univ with hT
  have hzero : ∀ a, a ∉ T → pi a = 0 := by
    intro a ha
    rw [himg] at ha
    simp only [Finset.mem_union, SuppPosR, SuppNegR, Finset.mem_filter, Finset.mem_univ,
      true_and, not_or, not_lt] at ha
    linarith [ha.1, ha.2]
  have hnz : ∀ a ∈ T, pi a ≠ 0 := by
    intro a ha h0
    rw [himg] at ha
    simp only [Finset.mem_union, SuppPosR, SuppNegR, Finset.mem_filter, Finset.mem_univ,
      true_and] at ha
    rcases ha with h | h <;> linarith
  -- key step: `π(arcs i) * orient i` is invariant under `i ↦ i + 1`
  have key : ∀ i : Fin (k + 1),
      pi (arcs (i + 1)) * orient src v arcs (i + 1) = pi (arcs i) * orient src v arcs i := by
    intro i
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      have : i + 1 = i := by
        have h1 := i.isLt; have h2 := (i + 1).isLt
        exact Fin.ext (by omega)
      rw [this]
    have h01 : (1 : Fin (k + 1)) ≠ 0 := by
      intro h
      have := congrArg Fin.val h
      simp [Nat.mod_eq_of_lt (by omega : 1 < k + 1)] at this
    have hne1 : i ≠ i + 1 := by
      intro h; apply h01
      have := congrArg (fun z => z - i) h
      simpa using this.symm
    have hne2 : i + 1 + 1 ≠ i + 1 := by
      intro h; apply h01
      have := congrArg (fun z => z - (i + 1)) h
      simpa using this
    set w := v (i + 1) with hw
    have hvi : v i ≠ w := fun h => hne1 (hinj h)
    have hvi2 : v (i + 1 + 1) ≠ w := fun h => hne2 (hinj h)
    set p := arcs i with hp
    set q := arcs (i + 1) with hq
    -- incidence values of `p` and `q` at `w`
    have hincp : inc src dst w p = - orient src v arcs i := by
      rcases ends_of_not (hends i) (fun h => hne1 (hinj h)) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hf : Forward src v arcs i := h1
        simp only [inc, orient, if_pos hf, hp, h1, h2, if_neg hvi]; simp
        all_goals first | rfl | exact hw.symm | exact hw
      · have hf : ¬ Forward src v arcs i := fun hf => hvi (by
          have : src (arcs i) = v i := hf
          rw [h1] at this; exact this.symm)
        simp only [inc, orient, if_neg hf, hp, h1, h2, if_neg hvi]; simp
        all_goals first | rfl | exact hw.symm | exact hw
    have hincq : inc src dst w q = orient src v arcs (i + 1) := by
      rcases ends_of_not (hends (i + 1)) (fun h => hne2 (hinj h).symm) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hf : Forward src v arcs (i + 1) := h1
        simp only [inc, orient, if_pos hf, hq, h1, h2, if_neg hvi2]; simp
        all_goals first | rfl | exact hw.symm | exact hw
      · have hf : ¬ Forward src v arcs (i + 1) := fun hf => hvi2 (by
          have : src (arcs (i + 1)) = v (i + 1) := hf
          rw [h1] at this; exact this)
        simp only [inc, orient, if_neg hf, hq, h1, h2, if_neg hvi2]; simp
        all_goals first | rfl | exact hw.symm | exact hw
    -- every other arc of the cycle misses `w`
    have hother : ∀ a ∈ T, a ≠ p → a ≠ q → inc src dst w a = 0 := by
      intro a ha hap haq
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp ha
      have hsrc : src (arcs j) ≠ w := by
        intro h
        have hm : w ∈ ({src (arcs j), dst (arcs j)} : Finset V) := by simp [h]
        rw [hends j] at hm
        simp only [Finset.mem_insert, Finset.mem_singleton] at hm
        rcases hm with h' | h'
        · exact haq (by rw [hq, hinj h'])
        · exact hap (by rw [hp]; congr 1; exact add_right_cancel (hinj h').symm)
      have hdst : dst (arcs j) ≠ w := by
        intro h
        have hm : w ∈ ({src (arcs j), dst (arcs j)} : Finset V) := by simp [h]
        rw [hends j] at hm
        simp only [Finset.mem_insert, Finset.mem_singleton] at hm
        rcases hm with h' | h'
        · exact haq (by rw [hq, hinj h'])
        · exact hap (by rw [hp]; congr 1; exact add_right_cancel (hinj h').symm)
      simp [inc, hsrc, hdst]
    have hB := hbd w
    rw [boundary_eq] at hB
    have hpT : p ∈ T := Finset.mem_image_of_mem _ (Finset.mem_univ _)
    have hqT : q ∈ T := Finset.mem_image_of_mem _ (Finset.mem_univ _)
    rw [← Finset.sum_subset (Finset.subset_univ T) (fun a _ ha => by rw [hzero a ha, zero_mul])]
      at hB
    by_cases hpq : p = q
    · -- degenerate traversal of a single arc: contradicts conservation
      exfalso
      rw [← Finset.sum_subset (Finset.singleton_subset_iff.mpr hpT)
        (fun a ha hna => by
          rw [hother a ha (by simpa using hna) (by rw [← hpq]; simpa using hna), mul_zero])] at hB
      rw [Finset.sum_singleton, hincp] at hB
      have ho : orient src v arcs i ≠ 0 := by unfold orient; split_ifs <;> norm_num
      have : pi p = 0 := by
        rcases mul_eq_zero.mp hB with h | h
        · exact h
        · exact absurd (neg_eq_zero.mp h) ho
      exact hnz p hpT this
    · have hsub : ({p, q} : Finset A) ⊆ T := by
        intro a ha; simp only [Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha with rfl | rfl <;> assumption
      rw [← Finset.sum_subset hsub (fun a ha hna => by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hna
          rw [hother a ha hna.1 hna.2, mul_zero])] at hB
      rw [Finset.sum_pair hpq, hincp, hincq] at hB
      linarith
  -- hence it is constant
  have hconst : ∀ i : Fin (k + 1),
      pi (arcs i) * orient src v arcs i = pi (arcs 0) * orient src v arcs 0 := by
    intro i
    induction i using Fin.induction with
    | zero => rfl
    | succ j ih =>
      rw [← Fin.coeSucc_eq_succ, key, ih]
  set s := pi (arcs 0) * orient src v arcs 0 with hs
  have horient : ∀ i, orient src v arcs i = 1 ∨ orient src v arcs i = -1 := by
    intro i; unfold orient; split_ifs <;> simp
  have hmemT : ∀ a ∈ SuppPosR pi ∪ SuppNegR pi, ∃ i, arcs i = a := by
    intro a ha
    rw [← himg] at ha
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp ha
    exact ⟨i, hi⟩
  have hpos1 : ∀ a ∈ SuppPosR pi, pi a = 1 := by
    intro a ha
    simp only [SuppPosR, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    rcases hval a with h | h | h <;> [exact h; linarith; linarith]
  have hneg1 : ∀ a ∈ SuppNegR pi, pi a = -1 := by
    intro a ha
    simp only [SuppNegR, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    rcases hval a with h | h | h <;> [linarith; linarith; exact h]
  -- equal values force equal orientation, opposite values force opposite orientation
  have hfwd : ∀ i j : Fin (k + 1), orient src v arcs i = orient src v arcs j →
      (Forward src v arcs i ↔ Forward src v arcs j) := by
    intro i j h
    unfold orient at h
    by_cases hi : Forward src v arcs i <;> by_cases hj : Forward src v arcs j <;>
      simp only [hi, hj, if_true, if_false] at h <;> first | tauto | norm_num at h
  have hbwd : ∀ i j : Fin (k + 1), orient src v arcs i = - orient src v arcs j →
      (Forward src v arcs i ↔ ¬ Forward src v arcs j) := by
    intro i j h
    unfold orient at h
    by_cases hi : Forward src v arcs i <;> by_cases hj : Forward src v arcs j <;>
      simp only [hi, hj, if_true, if_false] at h <;> first | tauto | norm_num at h
  have same_sign : ∀ a b, a ∈ SuppPosR pi ∪ SuppNegR pi → b ∈ SuppPosR pi ∪ SuppNegR pi →
      pi a = pi b → a ≠ b → ∃ i j, arcs i = a ∧ arcs j = b ∧
        (Forward src v arcs i ↔ Forward src v arcs j) := by
    intro a b ha hb hab _
    obtain ⟨i, rfl⟩ := hmemT a ha
    obtain ⟨j, rfl⟩ := hmemT b hb
    refine ⟨i, j, rfl, rfl, hfwd i j ?_⟩
    have h1 := hconst i
    have h2 := hconst j
    have hnz' : pi (arcs i) ≠ 0 := hnz _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
    rw [hab] at h1
    exact mul_left_cancel₀ (hab ▸ hnz') (h1.trans h2.symm)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · refine Finset.card_le_one.mpr (fun a ha b hb => ?_)
    by_contra hne
    rw [Finset.mem_inter] at ha hb
    obtain ⟨i, j, rfl, rfl, hij⟩ := same_sign a b (Finset.mem_union_left _ ha.1)
      (Finset.mem_union_left _ hb.1) (by rw [hpos1 _ ha.1, hpos1 _ hb.1]) hne
    have := hP _ ha.2 _ hb.2 hne k v arcs ⟨hinj, hends⟩ i j rfl rfl
    tauto
  · refine Finset.card_le_one.mpr (fun a ha b hb => ?_)
    by_contra hne
    rw [Finset.mem_inter] at ha hb
    obtain ⟨i, j, rfl, rfl, hij⟩ := same_sign a b (Finset.mem_union_right _ ha.1)
      (Finset.mem_union_right _ hb.1) (by rw [hneg1 _ ha.1, hneg1 _ hb.1]) hne
    have := hP _ ha.2 _ hb.2 hne k v arcs ⟨hinj, hends⟩ i j rfl rfl
    tauto
  · by_contra hcon
    rw [not_or] at hcon
    obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hcon.1
    obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.mpr hcon.2
    rw [Finset.mem_inter] at ha hb
    have hab : a ≠ b := by
      intro h; have := hpos1 a ha.1; rw [h, hneg1 b hb.1] at this; norm_num at this
    obtain ⟨i, rfl⟩ := hmemT a (Finset.mem_union_left _ ha.1)
    obtain ⟨j, rfl⟩ := hmemT b (Finset.mem_union_right _ hb.1)
    have h1 := hconst i
    have h2 := hconst j
    rw [hpos1 _ ha.1, one_mul] at h1
    rw [hneg1 _ hb.1, neg_one_mul] at h2
    have hopp : orient src v arcs i = - orient src v arcs j := by linarith
    have := hS _ ha.2 _ hb.2 hab k v arcs ⟨hinj, hends⟩ i j rfl rfl
    have := hbwd i j hopp
    tauto

#print axioms solution
