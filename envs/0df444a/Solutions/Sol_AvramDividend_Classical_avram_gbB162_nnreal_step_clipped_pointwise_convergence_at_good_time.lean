-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB162_nnreal_step_clipped_pointwise_convergence_at_good_time
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T12:56:46.296202+00:00
-- url     : https://prove2.me/submissions/3f465658-1c5f-4be4-85e6-309a8cba4432

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB139_floor_stopped_clipped_full_mesh_coefficient_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_gbB161_nnreal_mesh_sum_eq_real_mesh_sum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology Set AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem solution
    (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) (n : ℝ))
    (q : ℝ) (w : ℝ → ℝ) (a b : ℝ)
    (Y : ℝ → ℝ) (hY : ContinuousAt Y t)
    (hCont : Y t ∈ Ioo a b → ContinuousAt (deriv w) (Y t))
    (ha : Y t ≠ a) (hb : Y t ≠ b)
    (ρ : ℝ) (hρ : t ≠ ρ) :
    let K : ℕ → ℝ := fun m =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      (Finset.range (m + 1)).sum (fun i =>
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        if (s : ℝ) ≤ t ∧ t < ((s + Δ : ℝ≥0) : ℝ) then
          if (s : ℝ) < ρ then Real.exp (-(q * (s : ℝ))) *
            (if Y (s : ℝ) ∈ Icc a b then deriv w (Y (s : ℝ)) else 1)
          else 0 else 0)
    Tendsto K atTop (𝓝 (if t < ρ then
      Real.exp (-(q * t)) *
        (if Y t ∈ Icc a b then deriv w (Y t) else 1)
      else 0)) := by
  intro K
  let R : ℕ → ℝ := fun m =>
    let Δ : ℝ := (n : ℝ) / ((m : ℝ) + 1)
    (Finset.range (m + 1)).sum (fun i =>
      let s : ℝ := (i : ℝ) * Δ
      if s ≤ t ∧ t < (((i + 1 : ℕ) : ℝ) * Δ) then
        if s < ρ then Real.exp (-(q * s)) *
          (if Y s ∈ Icc a b then deriv w (Y s) else 1)
        else 0 else 0)
  have hR := avram_gbB139_floor_stopped_clipped_full_mesh_coefficient_tendsto
    n hn t ht q w a b Y hY hCont ha hb ρ hρ
  have hEq : K = R := by
    funext m
    let Δnn : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
    let Δr : ℝ := (n : ℝ) / ((m : ℝ) + 1)
    have hΔ : (Δnn : ℝ) = Δr := by
      simp only [Δnn, Δr, NNReal.coe_div, NNReal.coe_natCast,
        NNReal.coe_add, NNReal.coe_one, Nat.cast_add, Nat.cast_one]
    let c : ℕ → ℝ := fun i =>
      let s : ℝ := (((i : ℝ≥0) * Δnn : ℝ≥0) : ℝ)
      if s < ρ then Real.exp (-(q * s)) *
        (if Y s ∈ Icc a b then deriv w (Y s) else 1)
      else 0
    have hc (i : ℕ) : c i =
        (let s : ℝ := (i : ℝ) * Δr
         if s < ρ then Real.exp (-(q * s)) *
           (if Y s ∈ Icc a b then deriv w (Y s) else 1)
         else 0) := by
      simp only [c, NNReal.coe_mul, NNReal.coe_natCast, hΔ]
    have hgrid := avram_gbB161_nnreal_mesh_sum_eq_real_mesh_sum
      n m t c
    calc
      K m = (Finset.range (m + 1)).sum (fun i =>
          if (((i : ℝ≥0) * Δnn : ℝ≥0) : ℝ) ≤ t ∧
              t < ((((i : ℝ≥0) * Δnn) + Δnn : ℝ≥0) : ℝ)
          then c i else 0) := by rfl
      _ = (Finset.range (m + 1)).sum (fun i =>
          if (i : ℝ) * Δr ≤ t ∧
              t < (((i + 1 : ℕ) : ℝ) * Δr)
          then c i else 0) := by simpa only [Δnn, Δr] using hgrid
      _ = R m := by
          apply Finset.sum_congr rfl
          intro i hi
          simp only [hc i, R, Δr]
  simpa only [hEq] using hR
