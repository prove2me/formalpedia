-- Prove2me | solution 1 for ConvexOptAlg.LowerBounds.thm_3_14_final_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T01:25:56.881115+00:00
-- url     : https://prove2.me/submissions/2f5466dd-b7d2-4cb9-b94a-f85faf8aa3b0

import Mathlib
import Definitions.Def_ConvexOptAlg_LowerBounds_Defs

open scoped InnerProductSpace

namespace P8549Aux

open Finset

def tT (k j l : ℕ) : ℝ :=
  (if l = j ∧ j < k then 2 else 0) + (if l = j + 1 ∧ j + 1 < k then -1 else 0)
    + (if j = l + 1 ∧ j < k then -1 else 0)

lemma sum_filter_lt (n k : ℕ) (hkn : k ≤ n) (a : ℕ → ℝ) :
    ∑ j ∈ range n, (if j < k then a j else 0) = ∑ j ∈ range k, a j := by
  rw [← Finset.sum_filter]
  congr 1
  ext j; simp only [mem_filter, mem_range]; omega

lemma sum_filter_lt' (n k : ℕ) (hkn : k ≤ n) (a : ℕ → ℝ) :
    ∑ j ∈ range n, (if j + 1 < k then a j else 0) = ∑ j ∈ range (k - 1), a j := by
  rw [← Finset.sum_filter]
  congr 1
  ext j; simp only [mem_filter, mem_range]; omega

lemma double_sum (n k : ℕ) (hkn : k ≤ n) (g : ℕ → ℝ) :
    ∑ j ∈ range n, ∑ l ∈ range n, g j * tT k j l * g l
      = 2 * ∑ j ∈ range k, g j ^ 2 - 2 * ∑ j ∈ range (k - 1), g j * g (j + 1) := by
  simp only [tT, mul_add, add_mul, Finset.sum_add_distrib]
  have P1 : ∑ j ∈ range n, ∑ l ∈ range n, g j * (if l = j ∧ j < k then (2:ℝ) else 0) * g l
      = 2 * ∑ j ∈ range k, g j ^ 2 := by
    have h : ∀ j ∈ range n, ∑ l ∈ range n, g j * (if l = j ∧ j < k then (2:ℝ) else 0) * g l
        = if j < k then 2 * g j ^ 2 else 0 := by
      intro j hj
      rw [Finset.sum_eq_single j]
      · by_cases hjk : j < k <;> simp [hjk] <;> ring1
      · intro b _ hb; simp [hb]
      · intro h; exact absurd hj h
    rw [Finset.sum_congr rfl h, sum_filter_lt n k hkn, Finset.mul_sum]
  have P2 : ∑ j ∈ range n, ∑ l ∈ range n,
        g j * (if l = j + 1 ∧ j + 1 < k then (-1:ℝ) else 0) * g l
      = - ∑ j ∈ range (k - 1), g j * g (j + 1) := by
    have h : ∀ j ∈ range n, ∑ l ∈ range n,
          g j * (if l = j + 1 ∧ j + 1 < k then (-1:ℝ) else 0) * g l
        = if j + 1 < k then -(g j * g (j + 1)) else 0 := by
      intro j hj
      rw [Finset.sum_eq_single (j + 1)]
      · by_cases hjk : j + 1 < k <;> simp [hjk] <;> ring1
      · intro b _ hb; simp [hb]
      · intro h
        simp only [mem_range] at h
        have : ¬ (j + 1 < k) := by omega
        simp [this]
    rw [Finset.sum_congr rfl h, sum_filter_lt' n k hkn, Finset.sum_neg_distrib]
  have P3 : ∑ j ∈ range n, ∑ l ∈ range n,
        g j * (if j = l + 1 ∧ j < k then (-1:ℝ) else 0) * g l
      = - ∑ j ∈ range (k - 1), g j * g (j + 1) := by
    rw [Finset.sum_comm]
    have h : ∀ l ∈ range n, ∑ j ∈ range n,
          g j * (if j = l + 1 ∧ j < k then (-1:ℝ) else 0) * g l
        = if l + 1 < k then -(g l * g (l + 1)) else 0 := by
      intro l hl
      rw [Finset.sum_eq_single (l + 1)]
      · by_cases hjk : l + 1 < k <;> simp [hjk] <;> ring1
      · intro b _ hb; simp [hb]
      · intro h
        simp only [mem_range] at h
        have : ¬ (l + 1 < k) := by omega
        simp [this]
    rw [Finset.sum_congr rfl h, sum_filter_lt' n k hkn, Finset.sum_neg_distrib]
  rw [P1, P2, P3]; ring

lemma sum_Icc_shift (f : ℕ → ℝ) (m : ℕ) :
    ∑ i ∈ Icc 1 m, f i = ∑ j ∈ range m, f (j + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

lemma ident_minus (g : ℕ → ℝ) (m : ℕ) :
    2 * ∑ i ∈ Icc 1 (m + 1), g i ^ 2 - 2 * ∑ i ∈ Icc 1 m, g i * g (i + 1)
      = g 1 ^ 2 + g (m + 1) ^ 2 + ∑ i ∈ Icc 1 m, (g i - g (i + 1)) ^ 2 := by
  induction m with
  | zero => simp; ring
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1 + 1) (fun i => g i ^ 2),
      Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1) (fun i => g i * g (i + 1)),
      Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1) (fun i => (g i - g (i + 1)) ^ 2)]
    linear_combination ih

lemma ident_plus (g : ℕ → ℝ) (m : ℕ) :
    2 * ∑ i ∈ Icc 1 (m + 1), g i ^ 2 + 2 * ∑ i ∈ Icc 1 m, g i * g (i + 1)
      = g 1 ^ 2 + g (m + 1) ^ 2 + ∑ i ∈ Icc 1 m, (g i + g (i + 1)) ^ 2 := by
  induction m with
  | zero => simp; ring
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1 + 1) (fun i => g i ^ 2),
      Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1) (fun i => g i * g (i + 1)),
      Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1) (fun i => (g i + g (i + 1)) ^ 2)]
    linear_combination ih

open ConvexOptAlg.LowerBounds in
lemma ofLp_eq_coord {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (a : Fin n) :
    x.ofLp a = coord x ((a : ℕ) + 1) := by
  simp [coord, a.isLt]

open ConvexOptAlg.LowerBounds in
lemma tridiag_eq (n k : ℕ) (a b : Fin n) : tridiag n k a b = tT k a b := by
  simp only [tridiag, Matrix.of_apply, tT]
  split_ifs <;> first | (exfalso; omega) | norm_num

open ConvexOptAlg.LowerBounds in
lemma quad_eq (n k : ℕ) (hkn : k ≤ n) (x : EuclideanSpace ℝ (Fin n)) :
    quadForm (tridiag n k) x
      = 2 * ∑ i ∈ Icc 1 k, coord x i ^ 2
          - 2 * ∑ i ∈ Icc 1 (k - 1), coord x i * coord x (i + 1) := by
  have e : quadForm (tridiag n k) x = ∑ j ∈ range n, ∑ l ∈ range n,
      coord x (j + 1) * tT k j l * coord x (l + 1) := by
    simp only [quadForm, dotProduct, Matrix.mulVec, ofLp_eq_coord, tridiag_eq, Finset.mul_sum]
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    ring
  rw [e, double_sum n k hkn (fun j => coord x (j + 1)), sum_Icc_shift, sum_Icc_shift]

open ConvexOptAlg.LowerBounds in
lemma norm_sq_eq (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖x‖ ^ 2 = ∑ i ∈ Icc 1 n, coord x i ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => by positivity)),
    sum_Icc_shift, Finset.sum_range (fun j => coord x (j + 1) ^ 2)]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Real.norm_eq_abs, sq_abs, ← ofLp_eq_coord]


open ConvexOptAlg.LowerBounds in
lemma inner_e1 {n : ℕ} (hn : 1 ≤ n) (y : EuclideanSpace ℝ (Fin n)) :
    ⟪y, basisVec n 1⟫_ℝ = coord y 1 := by
  rw [PiLp.inner_apply, Finset.sum_eq_single (⟨0, hn⟩ : Fin n)]
  · simp [basisVec, coord, hn]
  · intro b _ hb
    have : (b : ℕ) ≠ 0 := by
      intro h; apply hb; ext; simp [h]
    simp [basisVec, this]
  · simp

lemma telesc (c : ℕ → ℝ) (m : ℕ) :
    ∑ i ∈ Icc 1 m, (c i - c (i + 1)) = c 1 - c (m + 1) := by
  rw [sum_Icc_shift]
  exact Finset.sum_range_sub' (fun j => c (j + 1)) m

lemma lower (c : ℕ → ℝ) (m : ℕ) :
    c 1 ^ 2 + c (m + 1) ^ 2 + ∑ i ∈ Icc 1 m, (c i - c (i + 1)) ^ 2 - 2 * c 1
      ≥ -(((m : ℝ) + 1) / ((m : ℝ) + 2)) := by
  set s : ℝ := 1 / ((m : ℝ) + 2) with hs
  have hpos : (0 : ℝ) < (m : ℝ) + 2 := by positivity
  have hexp : ∑ i ∈ Icc 1 m, (c i - c (i + 1) - s) ^ 2
      = ∑ i ∈ Icc 1 m, (c i - c (i + 1)) ^ 2 - 2 * s * ∑ i ∈ Icc 1 m, (c i - c (i + 1))
        + (m : ℝ) * s ^ 2 := by
    have : ∀ i ∈ Icc 1 m, (c i - c (i + 1) - s) ^ 2
        = (c i - c (i + 1)) ^ 2 - 2 * s * (c i - c (i + 1)) + s ^ 2 := fun i _ => by ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    simp
  have hnn : 0 ≤ ∑ i ∈ Icc 1 m, (c i - c (i + 1) - s) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  rw [telesc] at hexp
  have key : c 1 ^ 2 + c (m + 1) ^ 2 + ∑ i ∈ Icc 1 m, (c i - c (i + 1)) ^ 2 - 2 * c 1
      + ((m : ℝ) + 1) / ((m : ℝ) + 2)
      = ∑ i ∈ Icc 1 m, (c i - c (i + 1) - s) ^ 2 + (c (m + 1) - s) ^ 2
        + (c 1 - (1 - s)) ^ 2 := by
    rw [hexp, hs]
    field_simp
    ring
  nlinarith [sq_nonneg (c (m + 1) - s), sq_nonneg (c 1 - (1 - s))]

end P8549Aux

lemma p8549_icc_range (k : ℕ) (f : ℕ → ℝ) :
    ∑ i ∈ Finset.Icc 1 k, f i = ∑ j ∈ Finset.range k, f (j + 1) := by
  induction k with
  | zero => simp
  | succ m ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

lemma p8549_sq_sum (k : ℕ) :
    ∑ j ∈ Finset.range k, ((j : ℝ) + 1) ^ 2 = (k : ℝ) * (k + 1) * (2 * k + 1) / 6 := by
  induction k with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

open ConvexOptAlg.LowerBounds in
lemma p8549_norm_bound (n k : ℕ) (hkn : k ≤ n) :
    ‖xstarK n k‖ ^ 2 = ∑ i ∈ Finset.Icc 1 k, (1 - (i : ℝ) / ((k : ℝ) + 1)) ^ 2 ∧
      ∑ i ∈ Finset.Icc 1 k, (1 - (i : ℝ) / ((k : ℝ) + 1)) ^ 2 =
        ∑ i ∈ Finset.Icc 1 k, ((i : ℝ) / ((k : ℝ) + 1)) ^ 2 ∧
      ∑ i ∈ Finset.Icc 1 k, ((i : ℝ) / ((k : ℝ) + 1)) ^ 2 ≤ ((k : ℝ) + 1) / 3 := by
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [EuclideanSpace.norm_sq_eq]
    simp only [xstarK, Real.norm_eq_abs, sq_abs]
    rw [Fin.sum_univ_eq_sum_range
      (fun j : ℕ => (if j + 1 ≤ k then 1 - ((j : ℝ) + 1) / ((k : ℝ) + 1) else 0) ^ 2) n]
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkn
    rw [Finset.sum_range_add, p8549_icc_range]
    have h0 : ∑ x ∈ Finset.range d,
        (if k + x + 1 ≤ k then 1 - ((((k + x : ℕ)) : ℝ) + 1) / ((k : ℝ) + 1) else 0) ^ 2 = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      rw [if_neg (by omega)]; simp
    rw [h0, add_zero]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mem_range] at hx
    rw [if_pos (by omega)]
    push_cast; ring
  · rw [p8549_icc_range, p8549_icc_range]
    rw [← Finset.sum_range_reflect (fun j : ℕ => (((j + 1 : ℕ) : ℝ) / ((k : ℝ) + 1)) ^ 2) k]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mem_range] at hx
    have : ((k - 1 - x + 1 : ℕ) : ℝ) = (k : ℝ) - x := by
      rw [show k - 1 - x + 1 = k - x by omega, Nat.cast_sub hx.le]
    rw [this]
    field_simp
    push_cast; ring
  · rw [p8549_icc_range]
    have : ∑ j ∈ Finset.range k, (((j + 1 : ℕ) : ℝ) / ((k : ℝ) + 1)) ^ 2
        = (∑ j ∈ Finset.range k, ((j : ℝ) + 1) ^ 2) / ((k : ℝ) + 1) ^ 2 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro x _
      push_cast; rw [div_pow]
    rw [this, p8549_sq_sum, div_le_div_iff₀ (by positivity) (by norm_num)]
    have hk : (0 : ℝ) ≤ k := by positivity
    nlinarith [hk]

namespace P8549Aux
open Finset

open ConvexOptAlg.LowerBounds in
lemma coord_xstar (n k i : ℕ) (hkn : k ≤ n) (h1 : 1 ≤ i) (hik : i ≤ k) :
    coord (xstarK n k) i = 1 - (i : ℝ) / ((k : ℝ) + 1) := by
  have hin : 1 ≤ i ∧ i ≤ n := ⟨h1, by omega⟩
  simp only [coord, dif_pos hin, xstarK]
  rw [if_pos (by simp; omega)]
  have : (((i - 1 : ℕ) : ℝ) + 1) = (i : ℝ) := by rw [Nat.cast_sub h1]; simp
  simp [this]

open ConvexOptAlg.LowerBounds in
lemma fK_eq (n m : ℕ) (hkn : m + 1 ≤ n) (β : ℝ) (y : EuclideanSpace ℝ (Fin n)) :
    fK n β (m + 1) y = β / 8 * (coord y 1 ^ 2 + coord y (m + 1) ^ 2
      + ∑ i ∈ Icc 1 m, (coord y i - coord y (i + 1)) ^ 2 - 2 * coord y 1) := by
  have hq := quad_eq n (m + 1) hkn y
  simp only [Nat.add_sub_cancel] at hq
  have h2 := ident_minus (coord y) m
  rw [fK, hq, h2, inner_e1 (by omega)]
  ring

open ConvexOptAlg.LowerBounds in
lemma inf_val (n m : ℕ) (hkn : m + 1 ≤ n) (β : ℝ) (hβ : 0 < β) :
    (⨅ y, fK n β (m + 1) y) = -(β / 8) * (((m : ℝ) + 1) / ((m : ℝ) + 2)) := by
  have hlow : ∀ y, -(β / 8) * (((m : ℝ) + 1) / ((m : ℝ) + 2)) ≤ fK n β (m + 1) y := by
    intro y
    rw [fK_eq n m hkn]
    have := lower (coord y) m
    nlinarith
  have hval : fK n β (m + 1) (xstarK n (m + 1)) = -(β / 8) * (((m : ℝ) + 1) / ((m : ℝ) + 2)) := by
    rw [fK_eq n m hkn]
    have hpos : (0 : ℝ) < (m : ℝ) + 2 := by positivity
    have c1 := coord_xstar n (m + 1) 1 hkn le_rfl (by omega)
    have cm := coord_xstar n (m + 1) (m + 1) hkn (by omega) le_rfl
    have hs : ∑ i ∈ Icc 1 m, (coord (xstarK n (m + 1)) i - coord (xstarK n (m + 1)) (i + 1)) ^ 2
        = (m : ℝ) * (1 / ((m : ℝ) + 2)) ^ 2 := by
      have : ∀ i ∈ Icc 1 m,
          (coord (xstarK n (m + 1)) i - coord (xstarK n (m + 1)) (i + 1)) ^ 2
            = (1 / ((m : ℝ) + 2)) ^ 2 := by
        intro i hi
        rw [Finset.mem_Icc] at hi
        rw [coord_xstar n (m + 1) i hkn hi.1 (by omega),
          coord_xstar n (m + 1) (i + 1) hkn (by omega) (by omega)]
        push_cast
        field_simp
        ring
      rw [Finset.sum_congr rfl this, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
      simp
    rw [hs, c1, cm]
    push_cast
    field_simp
    ring
  apply le_antisymm
  · rw [← hval]
    exact ciInf_le ⟨_, Set.forall_mem_range.2 hlow⟩ _
  · exact le_ciInf hlow

end P8549Aux

open P8549Aux in
open ConvexOptAlg.LowerBounds in
theorem solution (n t : ℕ) (β : ℝ) (hβ : 0 < β) (ht : 1 ≤ t) (htn : 2 * t + 1 ≤ n) :
    (⨅ y, fK n β t y) - (⨅ y, fK n β (2 * t + 1) y) =
        β / 8 * (1 / ((t : ℝ) + 1) - 1 / (2 * (t : ℝ) + 2)) ∧
      β / 8 * (1 / ((t : ℝ) + 1) - 1 / (2 * (t : ℝ) + 2)) ≥
        3 * β / 32 * (‖xstarK n (2 * t + 1)‖ ^ 2 / ((t : ℝ) + 1) ^ 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, t = m + 1 := ⟨t - 1, by omega⟩
  have h1 := inf_val n m (by omega) β hβ
  have h2 := inf_val n (2 * (m + 1)) (by omega) β hβ
  have hpos : (0 : ℝ) < (m : ℝ) + 2 := by positivity
  refine ⟨?_, ?_⟩
  · rw [h1, show 2 * (m + 1) + 1 = 2 * (m + 1) + 1 from rfl, h2]
    push_cast
    field_simp
    ring
  · have hnb := (p8549_norm_bound n (2 * (m + 1) + 1) htn).2.2
    have he := (p8549_norm_bound n (2 * (m + 1) + 1) htn).1
    have he2 := (p8549_norm_bound n (2 * (m + 1) + 1) htn).2.1
    have hN : ‖xstarK n (2 * (m + 1) + 1)‖ ^ 2 ≤ ((2 * (((m + 1 : ℕ) : ℝ)) + 1) + 1) / 3 := by
      rw [he, he2]; push_cast at hnb ⊢; linarith
    push_cast at hN ⊢
    have hq : (0 : ℝ) < ((m : ℝ) + 1 + 1) ^ 2 := by positivity
    calc 3 * β / 32 * (‖xstarK n (2 * (m + 1) + 1)‖ ^ 2 / ((m : ℝ) + 1 + 1) ^ 2)
        ≤ 3 * β / 32 * (((2 * ((m : ℝ) + 1) + 1) + 1) / 3 / ((m : ℝ) + 1 + 1) ^ 2) := by
          gcongr
      _ = β / 8 * (1 / ((m : ℝ) + 1 + 1) - 1 / (2 * ((m : ℝ) + 1) + 2)) := by
          field_simp
          ring
