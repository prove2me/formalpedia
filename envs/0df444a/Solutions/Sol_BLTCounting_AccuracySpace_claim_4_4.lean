-- Prove2me | solution 1 for BLTCounting.AccuracySpace.claim_4_4
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T07:58:11.731242+00:00
-- url     : https://prove2.me/submissions/6dcf9194-b09d-42f8-a362-93b5e1fab242

import Mathlib
import Definitions.Def_BLTCounting_AccuracySpace_GeometricBlocks

open BLTCounting.AccuracySpace Finset Real

lemma harm_bounds (a n : ℕ) (ha : 1 ≤ a) :
    Real.log (((a + n : ℕ) : ℝ) / a) ≤ ∑ r ∈ Ico a (a + n), ((r : ℝ))⁻¹ ∧
    ∑ r ∈ Ico a (a + n), ((r : ℝ))⁻¹ ≤ (a : ℝ)⁻¹ + Real.log (((a + n : ℕ) : ℝ) / a) := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hanti : AntitoneOn (fun x : ℝ => x⁻¹) (Set.Icc (a : ℝ) (a + n)) := by
    intro x hx y hy hxy
    exact inv_anti₀ (lt_of_lt_of_le ha' hx.1) hxy
  have hint : ∫ x in (a : ℝ)..(a + n), x⁻¹ = Real.log (((a + n : ℕ) : ℝ) / a) := by
    rw [integral_inv_of_pos ha' (by positivity)]; push_cast; rfl
  have hsum : ∑ r ∈ Ico a (a + n), ((r : ℝ))⁻¹ = ∑ i ∈ range n, ((a : ℝ) + i)⁻¹ := by
    rw [sum_Ico_eq_sum_range]; simp
  have h1 := hanti.integral_le_sum
  have h2 := hanti.sum_le_integral
  rw [hint] at h1 h2
  rw [hsum]
  refine ⟨h1, ?_⟩
  have htel : ∑ i ∈ range n, ((a : ℝ) + i)⁻¹ + ((a : ℝ) + n)⁻¹ =
      (a : ℝ)⁻¹ + ∑ i ∈ range n, ((a : ℝ) + ((i + 1 : ℕ) : ℝ))⁻¹ := by
    rw [← sum_range_succ (fun i : ℕ => ((a : ℝ) + i)⁻¹), sum_range_succ']
    simp [add_comm]
  have : (0 : ℝ) ≤ ((a : ℝ) + n)⁻¹ := by positivity
  linarith

lemma ceil_log (t : ℝ) (R : ℕ) (hR : 1 ≤ R) (ht : (R : ℝ) ≤ t) :
    0 ≤ Real.log (⌈t⌉₊ : ℝ) - Real.log t ∧ Real.log (⌈t⌉₊ : ℝ) - Real.log t ≤ 1 / R := by
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have ht0 : 0 < t := lt_of_lt_of_le hR' ht
  have hc1 : t ≤ (⌈t⌉₊ : ℝ) := Nat.le_ceil t
  have hc2 : (⌈t⌉₊ : ℝ) < t + 1 := Nat.ceil_lt_add_one ht0.le
  have hc0 : (0 : ℝ) < ⌈t⌉₊ := lt_of_lt_of_le ht0 hc1
  rw [← Real.log_div hc0.ne' ht0.ne']
  constructor
  · exact Real.log_nonneg (by rw [le_div_iff₀ ht0]; linarith)
  · calc Real.log (⌈t⌉₊ / t) ≤ ⌈t⌉₊ / t - 1 := Real.log_le_sub_one_of_pos (by positivity)
      _ ≤ 1 / t := by rw [div_sub_one ht0.ne']; exact div_le_div_of_nonneg_right (by linarith) ht0.le
      _ ≤ 1 / R := one_div_le_one_div_of_le hR' ht

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℕ) (h : ℝ), 1 ≤ R → 0 < h → h ≤ 1 → ∀ i : ℕ,
      |blockMass R h i - h| ≤ C / R ∧ |blockMass R h i / h - 1| ≤ C / (R * h) := by
  refine ⟨2, by norm_num, fun R h hR hh _ i => ?_⟩
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  set t := blockPoint R h i with htdef
  set t' := blockPoint R h (i + 1) with ht'def
  have hlogt : Real.log t' = Real.log t + h := by
    rw [ht'def, htdef, blockPoint, blockPoint, Real.log_exp, Real.log_exp]; push_cast; ring
  have htR : (R : ℝ) ≤ t := by
    rw [htdef, blockPoint, Real.exp_add, Real.exp_log hR']
    exact le_mul_of_one_le_right hR'.le (Real.one_le_exp (by positivity))
  have ht0 : 0 < t := lt_of_lt_of_le hR' htR
  have htt' : t ≤ t' := by
    have := Real.exp_lt_exp.mpr (show Real.log t < Real.log t' by linarith)
    rw [Real.exp_log ht0, Real.exp_log (by rw [ht'def, blockPoint]; positivity)] at this; exact this.le
  have ht'R : (R : ℝ) ≤ t' := htR.trans htt'
  obtain ⟨ha1, ha2⟩ := ceil_log t R hR htR
  obtain ⟨hb1, hb2⟩ := ceil_log t' R hR ht'R
  set a := ⌈t⌉₊ with hadef
  set b := ⌈t'⌉₊ with hbdef
  have hab : a ≤ b := Nat.ceil_mono htt'
  have ha : 1 ≤ a := by
    have : (0 : ℝ) < a := lt_of_lt_of_le ht0 (Nat.le_ceil t)
    exact_mod_cast this
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (lt_of_lt_of_le ha hab)
  obtain ⟨hw1, hw2⟩ := harm_bounds a (b - a) ha
  have hba : a + (b - a) = b := by omega
  rw [hba] at hw1 hw2
  have hw : blockMass R h i = ∑ r ∈ Ico a b, ((r : ℝ))⁻¹ := rfl
  have hlogba : Real.log ((b : ℝ) / a) = Real.log b - Real.log a := Real.log_div hb0.ne' ha0.ne'
  have hainv : (a : ℝ)⁻¹ ≤ 1 / R := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le hR' (htR.trans (Nat.le_ceil t))
  have habs : |blockMass R h i - h| ≤ 2 / R := by
    rw [abs_le, hw]
    have e2 : (2 : ℝ) / R = 1 / R + 1 / R := by ring
    constructor <;> linarith
  refine ⟨habs, ?_⟩
  rw [show blockMass R h i / h - 1 = (blockMass R h i - h) / h by field_simp, abs_div,
    abs_of_pos hh, div_le_div_iff₀ hh (by positivity)]
  calc |blockMass R h i - h| * (R * h) = (|blockMass R h i - h| * R) * h := by ring
    _ ≤ 2 * h := by
        apply mul_le_mul_of_nonneg_right _ hh.le
        rwa [le_div_iff₀ hR'] at habs
