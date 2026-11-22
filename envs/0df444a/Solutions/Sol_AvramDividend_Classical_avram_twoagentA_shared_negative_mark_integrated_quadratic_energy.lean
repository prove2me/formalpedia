-- Prove2me | solution 1 for AvramDividend.Classical.avram_twoagentA_shared_negative_mark_integrated_quadratic_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T12:43:26.800351+00:00
-- url     : https://prove2.me/submissions/7beebf3c-d321-405d-9eeb-485c928945b3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_shared_negative_mark_quadratic_pointwise
open MeasureTheory Set AvramDividend.Classical
open scoped Classical NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    (ν : Measure ℝ) (i : ℕ)
    (hFin : ν (Ioc (-(1 / ((i : ℝ) + 1)))
                     (-(1 / ((i : ℝ) + 2)))) < ⊤)
    (hSq : IntegrableOn (fun z : ℝ => z ^ 2)
      (Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((i : ℝ) + 2)))) ν) :
    let B : Set ℝ :=
      Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((i : ℝ) + 2)))
    let c : ℝ := -(1 / ((i : ℝ) + 1))
    let δ : ℝ := 1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2)
    δ * (ν B).toReal ≤ 2 * (∫ z in B, z ^ 2 ∂ν) ∧
    c ^ 2 * (ν B).toReal ≤ 4 * (∫ z in B, z ^ 2 ∂ν) := by
  classical
  let B : Set ℝ :=
    Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((i : ℝ) + 2)))
  let c : ℝ := -(1 / ((i : ℝ) + 1))
  let δ : ℝ := 1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2)
  change δ * (ν B).toReal ≤ 2 * (∫ z in B, z ^ 2 ∂ν) ∧
    c ^ 2 * (ν B).toReal ≤ 4 * (∫ z in B, z ^ 2 ∂ν)
  have hBm : MeasurableSet B := measurableSet_Ioc
  haveI : IsFiniteMeasure (ν.restrict B) :=
    ⟨by simpa [B] using hFin⟩
  have hAE : ∀ᵐ z ∂(ν.restrict B),
      δ ≤ 2 * z ^ 2 ∧ c ^ 2 ≤ 4 * z ^ 2 := by
    filter_upwards [ae_restrict_mem hBm] with z hz
    obtain ⟨_, _, hδ, hc⟩ :=
      avram_twoagentA_shared_negative_mark_quadratic_pointwise
        i z hz
    exact ⟨hδ, hc⟩
  have h2 : Integrable (fun z : ℝ => 2 * z ^ 2) (ν.restrict B) :=
    hSq.const_mul 2
  have h4 : Integrable (fun z : ℝ => 4 * z ^ 2) (ν.restrict B) :=
    hSq.const_mul 4
  have hδBound :
      (∫ z : ℝ, δ ∂(ν.restrict B)) ≤
        (∫ z : ℝ, 2 * z ^ 2 ∂(ν.restrict B)) :=
    integral_mono_ae (integrable_const δ) h2
      (hAE.mono fun z hz => hz.1)
  have hcBound :
      (∫ z : ℝ, c ^ 2 ∂(ν.restrict B)) ≤
        (∫ z : ℝ, 4 * z ^ 2 ∂(ν.restrict B)) :=
    integral_mono_ae (integrable_const (c ^ 2)) h4
      (hAE.mono fun z hz => hz.2)
  constructor
  · simpa [integral_const, Measure.real, integral_mul_const, mul_comm] using hδBound
  · simpa [integral_const, Measure.real, integral_mul_const, mul_comm] using hcBound
