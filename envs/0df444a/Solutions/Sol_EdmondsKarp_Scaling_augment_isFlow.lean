-- Prove2me | solution 1 for EdmondsKarp.Scaling.augment_isFlow
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T19:19:11.936676+00:00
-- url     : https://prove2.me/submissions/78b3fcee-3b36-46d8-ac15-c571339cef1f

import Mathlib
import Definitions.Def_EdmondsKarp_Scaling_Transport
import Definitions.Def_EdmondsKarp_Scaling_Augmentation

set_option autoImplicit false

namespace EdmondsKarp.Scaling.P1FCC

open EdmondsKarp.Scaling

/-! ### Generic path-degree facts -/

section Generic

variable {V : Type} [Fintype V] [DecidableEq V]

lemma zip_cc (a b : V) (R : List V) :
    (a :: b :: R).zip (a :: b :: R).tail = (a, b) :: (b :: R).zip (b :: R).tail := rfl

lemma mem_of_mem_zip {L : List V} {x y : V} (h : (x, y) ∈ L.zip L.tail) :
    x ∈ L ∧ y ∈ L := by
  have := List.of_mem_zip h
  exact ⟨this.1, List.mem_of_mem_tail this.2⟩

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

lemma deg_zip : ∀ (L : List V), L.Nodup → ∀ (a b : V), L.head? = some a →
    L.getLast? = some b → ∀ u : V,
    (∑ v, (if (u, v) ∈ L.zip L.tail then (1:ℝ) else 0)) -
      (∑ v, (if (v, u) ∈ L.zip L.tail then (1:ℝ) else 0))
      = (if u = a then 1 else 0) - (if u = b then 1 else 0)
  | [], _, a, b, h, _, u => by simp at h
  | [x], _, a, b, h1, h2, u => by
      simp at h1 h2; subst h1; subst h2; simp
  | x :: y :: R, hnd, a, b, h1, h2, u => by
      have hx : x = a := by simpa using h1
      subst hx
      have hnd' : (y :: R).Nodup := hnd.of_cons
      have hxn : x ∉ y :: R := (List.nodup_cons.mp hnd).1
      have h2' : (y :: R).getLast? = some b := by
        rw [← h2]; simp [List.getLast?_cons_cons]
      have ih := deg_zip (y :: R) hnd' y b rfl h2' u
      rw [zip_cc]
      have e1 : ∀ v, (if (u, v) ∈ (x, y) :: (y :: R).zip (y :: R).tail then (1:ℝ) else 0)
          = (if (u, v) = (x, y) then 1 else 0)
            + (if (u, v) ∈ (y :: R).zip (y :: R).tail then 1 else 0) := by
        intro v
        by_cases h : (u, v) = (x, y)
        · have hn : (u, v) ∉ (y :: R).zip (y :: R).tail := by
            intro hm; rw [h] at hm; exact hxn (mem_of_mem_zip hm).1
          rw [if_pos (List.mem_cons.mpr (Or.inl h)), if_pos h, if_neg hn]; norm_num
        · rw [if_neg h]; simp only [List.mem_cons, h, false_or, zero_add]
      have e2 : ∀ v, (if (v, u) ∈ (x, y) :: (y :: R).zip (y :: R).tail then (1:ℝ) else 0)
          = (if (v, u) = (x, y) then 1 else 0)
            + (if (v, u) ∈ (y :: R).zip (y :: R).tail then 1 else 0) := by
        intro v
        by_cases h : (v, u) = (x, y)
        · have hn : (v, u) ∉ (y :: R).zip (y :: R).tail := by
            intro hm; rw [h] at hm; exact hxn (mem_of_mem_zip hm).1
          rw [if_pos (List.mem_cons.mpr (Or.inl h)), if_pos h, if_neg hn]; norm_num
        · rw [if_neg h]; simp only [List.mem_cons, h, false_or, zero_add]
      simp only [e1, e2, Finset.sum_add_distrib, sum_ind_left, sum_ind_right]
      linarith

end Generic

/-! ### Node is finite -/

variable {m n : ℕ}

def nodeEquiv : Unit ⊕ Unit ⊕ Fin m ⊕ Fin n ≃ Node m n where
  toFun
    | .inl _ => .s
    | .inr (.inl _) => .t
    | .inr (.inr (.inl i)) => .src i
    | .inr (.inr (.inr j)) => .dst j
  invFun
    | .s => .inl ()
    | .t => .inr (.inl ())
    | .src i => .inr (.inr (.inl i))
    | .dst j => .inr (.inr (.inr j))
  left_inv := by rintro (_ | _ | _ | _) <;> rfl
  right_inv := by rintro (_ | _ | _ | _) <;> rfl

instance nodeFintype : Fintype (Node m n) := Fintype.ofEquiv _ nodeEquiv

lemma sum_node (g : Node m n → ℝ) :
    ∑ v, g v = g .s + g .t + ∑ i, g (.src i) + ∑ j, g (.dst j) := by
  rw [← nodeEquiv.sum_comp]
  simp only [Fintype.sum_sum_type, Fintype.univ_unit, Finset.sum_singleton]
  simp [nodeEquiv]
  ring

/-! ### Path direction -/

lemma dir_sum {T : Transport m n} {x : Flow m n} {L : List (Node m n)} (hL : IsAugPath T x L)
    (u : Node m n) :
    ∑ v, pathDir L u v = (if u = .s then 1 else 0) - (if u = .t then 1 else 0) := by
  unfold pathDir
  rw [Finset.sum_sub_distrib]
  exact deg_zip L hL.1 .s .t hL.2.1 hL.2.2.1 u

lemma dir_zero {T : Transport m n} {x : Flow m n} {L : List (Node m n)} (hL : IsAugPath T x L)
    {u v : Node m n} (h1 : resCap T x u v = 0) (h2 : resCap T x v u = 0) :
    pathDir L u v = 0 := by
  have n1 : (u, v) ∉ L.zip L.tail := fun h => by
    have := hL.2.2.2 _ h; simp only at this; rw [h1] at this; exact lt_irrefl _ this
  have n2 : (v, u) ∉ L.zip L.tail := fun h => by
    have := hL.2.2.2 _ h; simp only at this; rw [h2] at this; exact lt_irrefl _ this
  simp [pathDir, n1, n2]

lemma dir_self (L : List (Node m n)) (u : Node m n) : pathDir L u u = 0 := by
  simp [pathDir]

lemma dir_anti (L : List (Node m n)) (u v : Node m n) : pathDir L u v = - pathDir L v u := by
  unfold pathDir; ring

lemma bound2 (y c ε : ℝ) (P Q : Prop) [Decidable P] [Decidable Q] (hε : 0 < ε) (hy : 0 ≤ y)
    (hyc : y ≤ c) (hP : P → ε ≤ c - y) (hQ : Q → ε ≤ y) :
    0 ≤ y + ε * ((if P then 1 else 0) - (if Q then 1 else 0)) ∧
      y + ε * ((if P then 1 else 0) - (if Q then 1 else 0)) ≤ c := by
  by_cases hp : P <;> by_cases hq : Q
  · simp only [if_pos hp, if_pos hq, sub_self, mul_zero, add_zero]; exact ⟨hy, hyc⟩
  · have := hP hp; simp only [if_pos hp, if_neg hq]; constructor <;> linarith
  · have := hQ hq; simp only [if_neg hp, if_pos hq]; constructor <;> linarith
  · simp only [if_neg hp, if_neg hq, sub_self, mul_zero, add_zero]; exact ⟨hy, hyc⟩

lemma bound1 (y ε : ℝ) (P Q : Prop) [Decidable P] [Decidable Q] (hε : 0 < ε) (hy : 0 ≤ y)
    (hQ : Q → ε ≤ y) :
    0 ≤ y + ε * ((if P then 1 else 0) - (if Q then 1 else 0)) := by
  by_cases hp : P <;> by_cases hq : Q
  · simp only [if_pos hp, if_pos hq, sub_self, mul_zero, add_zero]; exact hy
  · simp only [if_pos hp, if_neg hq]; linarith
  · have := hQ hq; simp only [if_neg hp, if_pos hq]; linarith
  · simp only [if_neg hp, if_neg hq, sub_self, mul_zero, add_zero]; exact hy

lemma eps_le {T : Transport m n} {x : Flow m n} {L : List (Node m n)} {ε : ℝ}
    (hε : IsPathMin T x L ε) {u v : Node m n} {r : ℝ} (hr : resCap T x u v = (r : WithTop ℝ))
    (h : (u, v) ∈ L.zip L.tail) : ε ≤ r := by
  have := hε.1 _ h
  simp only at this
  rw [hr] at this
  exact WithTop.coe_le_coe.mp this

lemma main {T : Transport m n} {x : Flow m n} {L : List (Node m n)} {ε : ℝ}
    (hx : IsFlow T x) (hL : IsAugPath T x L) (hε : IsPathMin T x L ε) :
    0 < ε ∧ IsFlow T (augment x L ε) ∧ (augment x L ε).ret = x.ret + ε := by
  have hpos : 0 < ε := by
    obtain ⟨e, he, heq⟩ := hε.2
    have := hL.2.2.2 e he
    rw [heq] at this
    exact_mod_cast this
  obtain ⟨h0f, h0x, h0z, h0r, hfa, hzb, hcs, hci, hcj, hct⟩ := hx
  -- direction sums
  have dS := dir_sum hL (.s)
  have dT := dir_sum hL (.t)
  rw [sum_node] at dS dT
  have dI : ∀ i, (∑ j, pathDir L (.src i) (.dst j)) - pathDir L .s (.src i) = 0 := by
    intro i
    have d := dir_sum hL (.src i)
    rw [sum_node] at d
    have z1 : pathDir L (.src i) .t = 0 := dir_zero hL rfl rfl
    have z2 : ∑ k, pathDir L (.src i) (.src k) = 0 :=
      Finset.sum_eq_zero (fun k _ => dir_zero hL rfl rfl)
    rw [z1, z2, dir_anti L (.src i) .s] at d
    simp at d
    linarith
  have dJ : ∀ j, pathDir L (.dst j) .t - ∑ i, pathDir L (.src i) (.dst j) = 0 := by
    intro j
    have d := dir_sum hL (.dst j)
    rw [sum_node] at d
    have z1 : pathDir L (.dst j) .s = 0 := dir_zero hL rfl rfl
    have z2 : ∑ k, pathDir L (.dst j) (.dst k) = 0 :=
      Finset.sum_eq_zero (fun k _ => dir_zero hL rfl rfl)
    have z3 : ∑ i, pathDir L (.dst j) (.src i) = - ∑ i, pathDir L (.src i) (.dst j) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun i _ => dir_anti L _ _)
    rw [z1, z2, z3] at d
    simpa [sub_eq_add_neg, add_comm] using d
  have sS : ∑ i, pathDir L .s (.src i) = 1 := by
    have z1 : pathDir L .s .t = 0 := dir_zero hL rfl rfl
    have z2 : ∑ j, pathDir L .s (.dst j) = 0 :=
      Finset.sum_eq_zero (fun j _ => dir_zero hL rfl rfl)
    rw [z1, z2, dir_self] at dS
    simpa using dS
  have sT : ∑ j, pathDir L (.dst j) .t = 1 := by
    have z1 : pathDir L .t .s = 0 := dir_zero hL rfl rfl
    have z2 : ∑ i, pathDir L .t (.src i) = 0 :=
      Finset.sum_eq_zero (fun i _ => dir_zero hL rfl rfl)
    have z3 : ∑ j, pathDir L .t (.dst j) = - ∑ j, pathDir L (.dst j) .t := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun j _ => dir_anti L _ _)
    rw [z1, z2, z3, dir_self] at dT
    have : (Node.t : Node m n) ≠ Node.s := by simp
    simp [this] at dT
    linarith
  refine ⟨hpos, ?_, rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (bound2 (x.f0 i) (T.a i) ε _ _ hpos (h0f i) (hfa i)
      (fun h => eps_le hε rfl h) (fun h => eps_le hε rfl h)).1
  · intro i j
    exact bound1 (x.fx i j) ε _ _ hpos (h0x i j) (fun h => eps_le hε rfl h)
  · intro j
    exact (bound2 (x.fz j) (T.b j) ε _ _ hpos (h0z j) (hzb j)
      (fun h => eps_le hε rfl h) (fun h => eps_le hε rfl h)).1
  · show 0 ≤ x.ret + ε; linarith
  · intro i
    exact (bound2 (x.f0 i) (T.a i) ε _ _ hpos (h0f i) (hfa i)
      (fun h => eps_le hε rfl h) (fun h => eps_le hε rfl h)).2
  · intro j
    exact (bound2 (x.fz j) (T.b j) ε _ _ hpos (h0z j) (hzb j)
      (fun h => eps_le hε rfl h) (fun h => eps_le hε rfl h)).2
  · show (∑ i, (x.f0 i + ε * pathDir L .s (.src i))) - (x.ret + ε) = 0
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, sS]; linarith
  · intro i
    show (∑ j, (x.fx i j + ε * pathDir L (.src i) (.dst j))) - (x.f0 i + ε * pathDir L .s (.src i)) = 0
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have := hci i; have := dI i
    linear_combination (hci i) + ε * (dI i)
  · intro j
    show (x.fz j + ε * pathDir L (.dst j) .t) - ∑ i, (x.fx i j + ε * pathDir L (.src i) (.dst j)) = 0
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    linear_combination (hcj j) + ε * (dJ j)
  · show (x.ret + ε) - ∑ j, (x.fz j + ε * pathDir L (.dst j) .t) = 0
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, sT]; linarith

end EdmondsKarp.Scaling.P1FCC

open EdmondsKarp.Scaling in
theorem solution {m n : ℕ} (T : Transport m n) (x : Flow m n) (L : List (Node m n)) (ε : ℝ)
    (hx : IsFlow T x) (hL : IsAugPath T x L) (hε : IsPathMin T x L ε) :
    0 < ε ∧ IsFlow T (augment x L ε) ∧ (augment x L ε).ret = x.ret + ε := by
  exact EdmondsKarp.Scaling.P1FCC.main hx hL hε
