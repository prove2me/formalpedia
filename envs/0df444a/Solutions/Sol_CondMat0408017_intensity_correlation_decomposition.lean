-- Prove2me | solution 1 for CondMat0408017.intensity_correlation_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-26T17:35:22.39322+00:00
-- url     : https://prove2.me/submissions/ad5e3340-b224-4c39-bfe5-8825815b7d51

import Mathlib
import Definitions.Def_CondMat0408017_Basic

open MeasureTheory Filter Topology Complex CondMat0408017

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (eps0 L1 wv : ℝ) (S1 S2 : Ω → ℂ) (_h1 : MemLp S1 4 P)
    (_h2 : MemLp S2 4 P) (hm1 : ∫ w, S1 w ∂P = 0) (hm2 : ∫ w, S2 w ∂P = 0) :
    (intensityCorrelation P eps0 L1 wv S1 S2 : ℂ) =
      ((eps0 / L1 ^ 2 * wv ^ 2 *
          ‖∫ w, fluct P S1 w * starRingEnd ℂ (fluct P S2 w) ∂P‖ ^ 2 : ℝ) : ℂ) +
        ((eps0 / L1 ^ 2 * wv ^ 2 * ‖∫ w, fluct P S1 w * fluct P S2 w ∂P‖ ^ 2 : ℝ) : ℂ) +
        ((eps0 / L1 ^ 2 * wv ^ 2 : ℝ) : ℂ) *
          cumulant4 P (fluct P S1) (fun w => starRingEnd ℂ (fluct P S1 w)) (fluct P S2)
            (fun w => starRingEnd ℂ (fluct P S2 w)) := by
  have hf1 : fluct P S1 = S1 := by
    ext w; simp [fluct, hm1]
  have hf2 : fluct P S2 = S2 := by
    ext w; simp [fluct, hm2]
  have hmc1 : ∫ w, starRingEnd ℂ (S1 w) ∂P = 0 := by
    rw [integral_conj, hm1, map_zero]
  have hmc2 : ∫ w, starRingEnd ℂ (S2 w) ∂P = 0 := by
    rw [integral_conj, hm2, map_zero]
  have hfc1 : fluct P (fun w => starRingEnd ℂ (S1 w)) = fun w => starRingEnd ℂ (S1 w) := by
    ext w; simp [fluct, hmc1]
  have hfc2 : fluct P (fun w => starRingEnd ℂ (S2 w)) = fun w => starRingEnd ℂ (S2 w) := by
    ext w; simp [fluct, hmc2]
  have hnorm1 : (fun w => S1 w * starRingEnd ℂ (S1 w)) = fun w => ((‖S1 w‖ ^ 2 : ℝ) : ℂ) := by
    ext w; rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hnorm2 : (fun w => S2 w * starRingEnd ℂ (S2 w)) = fun w => ((‖S2 w‖ ^ 2 : ℝ) : ℂ) := by
    ext w; rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hnorm12 : (fun w => S1 w * starRingEnd ℂ (S1 w) * S2 w * starRingEnd ℂ (S2 w)) =
      fun w => ((‖S1 w‖ ^ 2 * ‖S2 w‖ ^ 2 : ℝ) : ℂ) := by
    ext w
    have h1 := congrFun hnorm1 w
    have h2 := congrFun hnorm2 w
    calc S1 w * starRingEnd ℂ (S1 w) * S2 w * starRingEnd ℂ (S2 w)
        = (S1 w * starRingEnd ℂ (S1 w)) * (S2 w * starRingEnd ℂ (S2 w)) := by ring
      _ = ((‖S1 w‖ ^ 2 : ℝ) : ℂ) * ((‖S2 w‖ ^ 2 : ℝ) : ℂ) := by rw [h1, h2]
      _ = ((‖S1 w‖ ^ 2 * ‖S2 w‖ ^ 2 : ℝ) : ℂ) := by push_cast; rfl
  have hint_prod12 : (∫ w, S1 w * S2 w ∂P) * (∫ w, starRingEnd ℂ (S1 w) * starRingEnd ℂ (S2 w) ∂P) =
      ((‖∫ w, S1 w * S2 w ∂P‖ ^ 2 : ℝ) : ℂ) := by
    have hconj : (fun w => starRingEnd ℂ (S1 w) * starRingEnd ℂ (S2 w)) =
        fun w => starRingEnd ℂ (S1 w * S2 w) := by
      ext w; rw [map_mul]
    rw [hconj, integral_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hint_prod1c2 : (∫ w, S1 w * starRingEnd ℂ (S2 w) ∂P) *
      (∫ w, starRingEnd ℂ (S1 w) * S2 w ∂P) =
      ((‖∫ w, S1 w * starRingEnd ℂ (S2 w) ∂P‖ ^ 2 : ℝ) : ℂ) := by
    have hconj : (fun w => starRingEnd ℂ (S1 w) * S2 w) =
        fun w => starRingEnd ℂ (S1 w * starRingEnd ℂ (S2 w)) := by
      ext w; simp [map_mul]
    rw [hconj, integral_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hofR : ∀ f : Ω → ℝ, (∫ w, (f w : ℂ) ∂P) = ((∫ w, f w ∂P : ℝ) : ℂ) := fun f =>
    integral_ofReal
  rw [hf1, hf2]
  simp only [cumulant4, hf1, hf2, hfc1, hfc2, intensityCorrelation]
  rw [hnorm12, hnorm1, hnorm2, hofR, hofR, hofR, hint_prod12, hint_prod1c2]
  push_cast
  ring
