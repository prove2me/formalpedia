-- Prove2me | solution 1 for CondMat0408017.scattering_potential_equation
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-26T17:30:39.03631+00:00
-- url     : https://prove2.me/submissions/41e3164d-a15d-4ae3-ac22-afd5f99236f9

import Mathlib
import Definitions.Def_CondMat0408017_Basic

open MeasureTheory Filter Topology Complex CondMat0408017

theorem solution (Np Nm : ℝ → ℝ → ℂ) (α0 G0 R0 : ℝ → ℂ)
    (Tm V : ℝ → ℝ → ℂ)
    (hRRE : ∀ p k, DKernel.applyLeft Np
        ⟨R0, fun q k => -2 * I * G0 q * Tm q k * G0 k * α0 k⟩ p k = Nm p k)
    (h92 : ∀ k, 2 * I * α0 k * G0 k + R0 k = -1) :
    (∀ p k, α0 k ≠ 0 → G0 k ≠ 0 →
      ∫ q, Np p q * G0 q * Tm q k / (2 * Real.pi) =
        (R0 k * Np p k - Nm p k) / (2 * I * α0 k * G0 k)) ∧
    (∀ p q, α0 q ≠ 0 →
      ((2 * I * α0 q * G0 q + R0 q) * Np p q - Nm p q) / (2 * I * α0 q) =
        -(Np p q + Nm p q) / (2 * I * α0 q)) ∧
    ((∀ q k, Tm q k = V q k + ∫ p, Tm q p * G0 p * V p k / (2 * Real.pi)) →
      ∀ p k, α0 k ≠ 0 → G0 k ≠ 0 → (∀ᵐ q, α0 q ≠ 0 ∧ G0 q ≠ 0) →
        Integrable (fun q => Np p q * G0 q * V q k) →
        Integrable (fun q => Np p q * G0 q * Tm q k) →
        Integrable (Function.uncurry fun q q' => Np p q' * G0 q' * Tm q' q * G0 q * V q k) →
        ∫ q, -(Np p q + Nm p q) / (2 * I * α0 q) * V q k / (2 * Real.pi) =
          (R0 k * Np p k - Nm p k) / (2 * I * α0 k * G0 k)) := by
  have hpart1 : ∀ p k, α0 k ≠ 0 → G0 k ≠ 0 →
      ∫ q, Np p q * G0 q * Tm q k / (2 * Real.pi) =
        (R0 k * Np p k - Nm p k) / (2 * I * α0 k * G0 k) := by
    intro p k hα0 hG0
    have h := hRRE p k
    simp only [DKernel.applyLeft] at h
    have hrew : (fun q => Np p q * (-2 * I * G0 q * Tm q k * G0 k * α0 k) / (2 * Real.pi)) =
        fun q => -(2 * I * α0 k * G0 k) * (Np p q * G0 q * Tm q k / (2 * Real.pi)) := by
      ext q; ring
    rw [hrew, integral_const_mul] at h
    have hden : 2 * I * α0 k * G0 k ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) hα0) hG0
    rw [eq_div_iff hden]
    linear_combination -h
  have hpart2 : ∀ p q, α0 q ≠ 0 →
      ((2 * I * α0 q * G0 q + R0 q) * Np p q - Nm p q) / (2 * I * α0 q) =
        -(Np p q + Nm p q) / (2 * I * α0 q) := by
    intro p q _
    rw [h92 q]
    ring
  refine ⟨hpart1, hpart2, ?_⟩
  intro hT p k hα0 hG0 hae hIntV _hIntT hIntProd
  rw [← hpart1 p k hα0 hG0]
  have hpi_ne : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hIntV' : Integrable (fun q => Np p q * G0 q * V q k / (2 * (Real.pi : ℂ))) :=
    hIntV.div_const (2 * (Real.pi : ℂ))
  have hIntProd' : Integrable (Function.uncurry fun q q' =>
      Np p q' * G0 q' * Tm q' q * G0 q * V q k / ((2 * (Real.pi : ℂ)) * (2 * (Real.pi : ℂ)))) :=
    hIntProd.div_const ((2 * (Real.pi : ℂ)) * (2 * (Real.pi : ℂ)))
  have hIntSwap : Integrable (Function.uncurry fun q' q =>
      Np p q' * G0 q' * Tm q' q * G0 q * V q k / ((2 * (Real.pi : ℂ)) * (2 * (Real.pi : ℂ)))) :=
    hIntProd'.swap
  have hstep1 : ∫ q', Np p q' * G0 q' * Tm q' k / (2 * (Real.pi : ℂ)) =
      (∫ q', Np p q' * G0 q' * V q' k / (2 * (Real.pi : ℂ))) +
      ∫ q', ∫ q, Np p q' * G0 q' * Tm q' q * G0 q * V q k /
        ((2 * (Real.pi : ℂ)) * (2 * (Real.pi : ℂ))) := by
    have hcongr : (fun q' => Np p q' * G0 q' * Tm q' k / (2 * (Real.pi : ℂ))) =
        fun q' => Np p q' * G0 q' * V q' k / (2 * (Real.pi : ℂ)) +
          ∫ q, Np p q' * G0 q' * Tm q' q * G0 q * V q k /
            ((2 * (Real.pi : ℂ)) * (2 * (Real.pi : ℂ))) := by
      ext q'
      rw [hT q' k, mul_add, add_div]
      congr 1
      have hpull : Np p q' * G0 q' * (∫ q, Tm q' q * G0 q * V q k / (2 * (Real.pi : ℂ))) /
            (2 * (Real.pi : ℂ)) =
          (Np p q' * G0 q' / (2 * (Real.pi : ℂ))) *
            ∫ q, Tm q' q * G0 q * V q k / (2 * (Real.pi : ℂ)) := by ring
      rw [hpull, ← integral_const_mul]
      congr 1
      ext q
      ring
    rw [hcongr]
    exact integral_add hIntV' hIntSwap.integral_prod_left
  have hswap : (∫ q', ∫ q, Np p q' * G0 q' * Tm q' q * G0 q * V q k /
        ((2 * (Real.pi : ℂ)) * (2 * (Real.pi : ℂ)))) =
      ∫ q, ∫ q', Np p q' * G0 q' * Tm q' q * G0 q * V q k /
        ((2 * (Real.pi : ℂ)) * (2 * (Real.pi : ℂ))) :=
    (MeasureTheory.integral_integral_swap hIntProd').symm
  have hIntOuter : Integrable (fun q => ∫ q', Np p q' * G0 q' * Tm q' q * G0 q * V q k /
        ((2 * (Real.pi : ℂ)) * (2 * (Real.pi : ℂ)))) :=
    hIntProd'.integral_prod_left
  rw [hstep1, hswap]
  rw [← integral_add hIntV' hIntOuter]
  refine integral_congr_ae ?_
  filter_upwards [hae] with q ⟨hαq, hGq⟩
  have hinner : (∫ q', Np p q' * G0 q' * Tm q' q * G0 q * V q k /
        ((2 * (Real.pi : ℂ)) * (2 * (Real.pi : ℂ)))) =
      (G0 q * V q k / (2 * (Real.pi : ℂ))) *
        ∫ q', Np p q' * G0 q' * Tm q' q / (2 * (Real.pi : ℂ)) := by
    rw [← integral_const_mul]
    congr 1
    ext q'
    ring
  rw [hinner, hpart1 p q hαq hGq]
  have h2Iα : 2 * I * α0 q ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) hαq
  have h2IαG : 2 * I * α0 q * G0 q ≠ 0 := mul_ne_zero h2Iα hGq
  have hcomb : Np p q * G0 q * V q k / (2 * (Real.pi : ℂ)) +
      G0 q * V q k / (2 * (Real.pi : ℂ)) * ((R0 q * Np p q - Nm p q) / (2 * I * α0 q * G0 q)) =
      ((2 * I * α0 q * G0 q + R0 q) * Np p q - Nm p q) / (2 * I * α0 q) *
        V q k / (2 * (Real.pi : ℂ)) := by
    field_simp [hpi_ne, h2Iα, hGq]
    ring
  rw [hcomb, hpart2 p q hαq]
