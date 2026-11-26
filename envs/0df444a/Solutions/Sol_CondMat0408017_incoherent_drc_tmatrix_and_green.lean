-- Prove2me | solution 1 for CondMat0408017.incoherent_drc_tmatrix_and_green
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-26T17:30:51.924026+00:00
-- url     : https://prove2.me/submissions/c316739d-0c05-4d86-ae98-2d7ac393d9e9

import Mathlib
import Definitions.Def_CondMat0408017_Basic

open MeasureTheory Filter Topology Complex CondMat0408017

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] :
    (∀ (L1 ω c θ0 θs : ℝ) (G0q G0k : ℂ) (T : Ω → ℂ), 0 < c →
      θ0 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) →
      incoherentMeanDRC P L1 ω c θ0 θs
          (fun w => -2 * I * G0q * T w * G0k * ((ω / c * Real.cos θ0 : ℝ) : ℂ)) =
        1 / L1 * (2 / Real.pi) * (ω / c) ^ 3 * Real.cos θs ^ 2 * Real.cos θ0 * ‖G0q‖ ^ 2 *
          ((∫ w, ‖T w‖ ^ 2 ∂P) - ‖∫ w, T w ∂P‖ ^ 2) * ‖G0k‖ ^ 2) ∧
    (∀ (α0 G0 R0 : ℝ → ℂ) (Tm V : ℝ → ℝ → ℂ) (G : DKernel),
      (∀ k, 2 * I * α0 k * G0 k + R0 k = -1) →
      (∀ p k, Tm p k = V p k + ∫ q, V p q * G0 q * Tm q k / (2 * Real.pi)) →
      IsLippmannSchwinger G0 V G →
      (∀ h : ℝ → ℝ → ℂ, (∀ q k, h q k = G0 q * ∫ p, V q p * h p k / (2 * Real.pi)) → h = 0) →
      (∀ q k, Integrable (fun p => V q p * G.reg p k) ∧
        Integrable (fun p => V q p * G0 p * Tm p k)) →
      (DKernel.mk R0 (fun q k => -2 * I * G0 q * Tm q k * G0 k * α0 k) =
        DKernel.mk (fun k => -1 - 2 * I * G.diag k * α0 k)
          (fun q k => -2 * I * G.reg q k * α0 k))) := by
  constructor
  · intro L1 ω c θ0 θs G0q G0k T hc hθ0
    have hcos0 : 0 < Real.cos θ0 := Real.cos_pos_of_mem_Ioo hθ0
    set C : ℂ := -2 * I * G0q * G0k * ((ω / c * Real.cos θ0 : ℝ) : ℂ)
    have hfun : ∀ w, -2 * I * G0q * T w * G0k * ((ω / c * Real.cos θ0 : ℝ) : ℂ) = C * T w := by
      intro w; simp only [C]; ring
    have hC_norm : ‖C‖ ^ 2 = 4 * ‖G0q‖ ^ 2 * ‖G0k‖ ^ 2 * (ω / c) ^ 2 * Real.cos θ0 ^ 2 := by
      simp only [C, norm_mul, norm_neg, Complex.norm_ofNat, Complex.norm_I, Complex.norm_real,
        Real.norm_eq_abs, mul_pow, sq_abs]
      ring
    simp only [incoherentMeanDRC, hfun]
    have hint1 : (∫ w, ‖C * T w‖ ^ 2 ∂P) = ‖C‖ ^ 2 * ∫ w, ‖T w‖ ^ 2 ∂P := by
      have : (fun w => ‖C * T w‖ ^ 2) = fun w => ‖C‖ ^ 2 * ‖T w‖ ^ 2 := by
        ext w; rw [norm_mul, mul_pow]
      rw [this, integral_const_mul]
    have hint2 : ‖∫ w, C * T w ∂P‖ ^ 2 = ‖C‖ ^ 2 * ‖∫ w, T w ∂P‖ ^ 2 := by
      rw [integral_const_mul, norm_mul, mul_pow]
    rw [hint1, hint2, ← mul_sub, hC_norm]
    field_simp [hc.ne', hcos0.ne', Real.pi_ne_zero]
    ring
  · intro α0 G0 R0 Tm V G h92 hT hLS huniq hInt
    have hdiag : R0 = fun k => -1 - 2 * I * G.diag k * α0 k := by
      ext k
      rw [hLS.1 k]
      linear_combination h92 k
    have hreg_eq : G.reg = fun q k => G0 q * Tm q k * G0 k := by
      let h : ℝ → ℝ → ℂ := fun q k => G.reg q k - G0 q * Tm q k * G0 k
      have hh : ∀ q k, h q k = G0 q * ∫ p, V q p * h p k / (2 * Real.pi) := by
        intro q k
        have h1 := hLS.2 q k
        simp only [DKernel.applyLeft, hLS.1] at h1
        have h2 : G0 q * Tm q k * G0 k =
            G0 q * (V q k * G0 k + ∫ p, V q p * (G0 p * Tm p k * G0 k) / (2 * Real.pi)) := by
          rw [hT q k]
          have hpull : (∫ p, V q p * (G0 p * Tm p k * G0 k) / (2 * Real.pi)) =
              (∫ p, V q p * G0 p * Tm p k / (2 * Real.pi)) * G0 k := by
            rw [← integral_mul_const]
            congr 1
            ext p
            ring
          rw [hpull]
          ring
        have hIntA : Integrable (fun p => V q p * G.reg p k / (2 * (Real.pi : ℂ))) :=
          (hInt q k).1.div_const _
        have hIntB : Integrable (fun p => V q p * (G0 p * Tm p k * G0 k) / (2 * (Real.pi : ℂ))) := by
          have : (fun p => V q p * (G0 p * Tm p k * G0 k) / (2 * (Real.pi : ℂ))) =
              fun p => (V q p * G0 p * Tm p k) * (G0 k / (2 * (Real.pi : ℂ))) := by
            ext p; ring
          rw [this]
          exact (hInt q k).2.mul_const _
        have hsub : (fun p => V q p * h p k / (2 * (Real.pi : ℂ))) =
            fun p => V q p * G.reg p k / (2 * (Real.pi : ℂ)) -
              V q p * (G0 p * Tm p k * G0 k) / (2 * (Real.pi : ℂ)) := by
          ext p; simp only [h]; ring
        simp only [h]
        rw [h1, h2, hsub, integral_sub hIntA hIntB]
        ring
      have h0 : h = 0 := huniq h hh
      ext q k
      have hqk : h q k = 0 := congrFun (congrFun h0 q) k
      exact sub_eq_zero.mp hqk
    congr 1
    ext q k
    rw [hreg_eq]
    ring
