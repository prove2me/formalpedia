-- Prove2me | solution 1 for FracPackCover.General.lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T01:04:08.124859+00:00
-- url     : https://prove2.me/submissions/64a3d90d-80f8-449e-aabd-07a9066dcfbf

import Mathlib
import Definitions.Def_FracPackCover_General_Basic

open FracPackCover.General

theorem solution {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
    (P : Set (Fin n → ℝ)) (hP : Convex ℝ P) (hd : ∀ i, 0 < d i)
    (ρ : ℝ) (hρ : 0 < ρ) (hW : WidthBound A b d P ρ)
    (x : Fin n → ℝ) (hx : x ∈ P) (hlam : 0 < lam A b d x) (α : ℝ)
    (hα : 2 / lam A b d x * Real.log (6 * m * ρ / lam A b d x) ≤ α) :
    G1 A b d x (lam A b d x) (dualVec A b d α x) := by
  let t := fun i => (FracPackCover.Covering.rowVal A x i - b i) / d i
  let l := lam A b d x
  have hl : 0 < l := hlam
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast (NeZero.one_le : 1 ≤ m)
  have ht (i) : -ρ ≤ t i ∧ t i ≤ ρ := by
    have h := abs_le.mp (hW x hx i)
    dsimp [t]
    constructor
    · apply (le_div_iff₀ (hd i)).mpr; nlinarith [h.1]
    · exact (div_le_iff₀ (hd i)).mpr h.2
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty t
  have hj' : t j = l := hj.symm
  have hlρ : l ≤ ρ := by rw [← hj']; exact (ht j).2
  have hq : 1 ≤ 6 * (m : ℝ) * ρ / l := by
    apply (le_div_iff₀ hl).mpr
    nlinarith
  have hq0 : 0 < 6 * (m : ℝ) * ρ / l := by positivity
  have hlog : 0 ≤ Real.log (6 * (m : ℝ) * ρ / l) := Real.log_nonneg hq
  have ha : 0 ≤ α := (mul_nonneg (by positivity) hlog).trans hα
  have had : Real.log (6 * (m : ℝ) * ρ / l) ≤ α * (l / 2) := by
    have h := mul_le_mul_of_nonneg_right hα (show 0 ≤ l / 2 by positivity)
    have he : (2 / l * Real.log (6 * (m : ℝ) * ρ / l)) * (l / 2) =
        Real.log (6 * (m : ℝ) * ρ / l) := by field_simp
    rwa [he] at h
  have hsmall : Real.exp (-(α * (l / 2))) ≤ l / (6 * m * ρ) := by
    have h := Real.exp_le_exp.mpr (neg_le_neg had)
    rw [Real.exp_neg (Real.log _), Real.exp_log hq0] at h
    convert h using 1 <;> field_simp <;> ring
  let Z := ∑ i, Real.exp (α * t i)
  have hZ : Real.exp (α * l) ≤ Z := by
    have h := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => (Real.exp_pos (α * t i)).le)
      (Finset.mem_univ j)
    simpa [hj', Z] using h
  have hi (i) : (l / 2 - t i) * Real.exp (α * t i) ≤
      (ρ + l / 2) * Real.exp (α * (l / 2)) := by
    by_cases h : t i ≤ l / 2
    · exact mul_le_mul (by linarith [(ht i).1])
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h ha))
        (Real.exp_pos _).le (by positivity)
    · exact (mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.exp_pos _).le).trans (by positivity)
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have he : Real.exp (α * (l / 2)) = Real.exp (α * l) * Real.exp (-(α * (l / 2))) := by
    rw [← Real.exp_add]; congr 1; ring
  have hc : (m : ℝ) * (ρ + l / 2) * (l / (6 * m * ρ)) ≤ l / 4 := by
    have hid : (m : ℝ) * (ρ + l / 2) * (l / (6 * m * ρ)) = (ρ + l / 2) * l / (6 * ρ) := by
      field_simp
    rw [hid]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hb : (m : ℝ) * ((ρ + l / 2) * Real.exp (α * (l / 2))) ≤
      (l / 4) * Real.exp (α * l) := by
    rw [he]
    calc
      _ = Real.exp (α * l) * ((m : ℝ) * (ρ + l / 2) * Real.exp (-(α * (l / 2)))) := by ring
      _ ≤ Real.exp (α * l) * ((m : ℝ) * (ρ + l / 2) * (l / (6 * m * ρ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsmall (by positivity)) (Real.exp_pos _).le
      _ ≤ Real.exp (α * l) * (l / 4) := mul_le_mul_of_nonneg_left hc (Real.exp_pos _).le
      _ = _ := by ring
  have hz := mul_le_mul_of_nonneg_left hZ (show 0 ≤ l / 4 by positivity)
  have hh := hsum.trans hb
  simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum] at hh
  have hmain : l * Z ≤ 4 * ∑ i, t i * Real.exp (α * t i) := by
    change _ ≤ l / 4 * Z at hz
    change l / 2 * Z - _ ≤ _ at hh
    linarith
  unfold G1 lagr dualVec
  convert hmain using 1
  · congr 1
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [t]
    rw [mul_div_assoc]
    field_simp [(hd i).ne']
  · congr 1
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [t]
    rw [mul_div_assoc]
    ring

#print axioms solution
