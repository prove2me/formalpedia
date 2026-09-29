-- Prove2me | solution 1 for CalibratedCE.Forecast.l1_calib_le_sqrt_l2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T17:53:07.313105+00:00
-- url     : https://prove2.me/submissions/d1a5cc50-adff-4b2d-bfef-38ce832a0c19

import Mathlib
import Definitions.Def_CalibratedCE_Forecast_CalibScoreH



namespace CalibratedCE.Forecast

open Classical

lemma NH_sum {n : ℕ} (h : List ((Fin n → ℝ) × Fin n)) :
    ∑ p ∈ (h.map Prod.fst).toFinset, (NH h p : ℝ) = h.length := by
  have e : ∀ p, NH h p = (h.map Prod.fst).count p := by
    intro p
    unfold NH
    rw [List.count_eq_countP, List.countP_map, List.countP_eq_length_filter]
    have hf : ((fun x => x == p) ∘ Prod.fst) = (fun e : (Fin n → ℝ) × Fin n => decide (e.1 = p)) := by
      funext e
      simp only [Function.comp]
      by_cases he : e.1 = p <;> simp [he]
    rw [hf]
  simp_rw [e]
  rw [← Nat.cast_sum, List.sum_toFinset_count_eq_length, List.length_map]

theorem l1_calib_le_sqrt_l2 {n : ℕ} (h : List ((Fin n → ℝ) × Fin n)) (j : Fin n) :
    calibScoreHj h j ≤ Real.sqrt (calibScore2Hj h j) := by
  unfold calibScoreHj calibScore2Hj
  set S := (h.map Prod.fst).toFinset with hS
  have hN := NH_sum h
  rw [← hS] at hN
  set w : (Fin n → ℝ) → ℝ := fun p => (NH h p : ℝ) / (h.length : ℝ) with hw
  set a : (Fin n → ℝ) → ℝ := fun p => |rhoH h p j - p j| with ha
  have hw0 : ∀ p, 0 ≤ w p := fun p => by simp only [hw]; positivity
  have hws : ∑ p ∈ S, w p ≤ 1 := by
    simp only [hw, ← Finset.sum_div]
    rw [hN]
    rcases Nat.eq_zero_or_pos h.length with h0 | hpos
    · rw [h0]; simp
    · rw [div_self (by positivity)]
  have e1 : ∑ p ∈ S, |rhoH h p j - p j| * (NH h p : ℝ) / (h.length : ℝ) =
      ∑ p ∈ S, Real.sqrt (w p) * (a p * Real.sqrt (w p)) := by
    apply Finset.sum_congr rfl; intro p _
    rw [show Real.sqrt (w p) * (a p * Real.sqrt (w p)) = a p * (Real.sqrt (w p) * Real.sqrt (w p))
      by ring, Real.mul_self_sqrt (hw0 p)]
    simp only [ha, hw]; ring
  have e2 : ∑ p ∈ S, (rhoH h p j - p j) ^ 2 * (NH h p : ℝ) / (h.length : ℝ) =
      ∑ p ∈ S, (a p * Real.sqrt (w p)) ^ 2 := by
    apply Finset.sum_congr rfl; intro p _
    rw [mul_pow, Real.sq_sqrt (hw0 p)]
    simp only [ha, hw]; rw [sq_abs]; ring
  rw [e1, e2]
  apply Real.le_sqrt_of_sq_le
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun p => Real.sqrt (w p)) (fun p => a p * Real.sqrt (w p))
  have e3 : ∑ p ∈ S, Real.sqrt (w p) ^ 2 = ∑ p ∈ S, w p :=
    Finset.sum_congr rfl (fun p _ => Real.sq_sqrt (hw0 p))
  rw [e3] at hcs
  have hnn : 0 ≤ ∑ p ∈ S, (a p * Real.sqrt (w p)) ^ 2 := Finset.sum_nonneg (fun p _ => sq_nonneg _)
  nlinarith

end CalibratedCE.Forecast

open CalibratedCE.Forecast

theorem solution {n : ℕ} (h : List ((Fin n → ℝ) × Fin n)) (j : Fin n) :
    calibScoreHj h j ≤ Real.sqrt (calibScore2Hj h j) := by
  exact l1_calib_le_sqrt_l2 h j
