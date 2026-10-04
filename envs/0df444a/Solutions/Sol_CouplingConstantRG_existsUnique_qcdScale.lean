-- Prove2me | solution 1 for CouplingConstantRG.existsUnique_qcdScale
-- status  : ACCEPTED   (prove)
-- author  : @os0xcom
-- created : 2026-10-03T15:50:21.582075+00:00
-- url     : https://prove2.me/submissions/7fa5a881-c9e7-4ec1-8f0c-2b9f3601ae5d

import Mathlib
import Definitions.Def_CouplingConstantDefs
import Definitions.Def_CouplingConstantRGDefs

open CouplingConstant Real

theorem solution (β₀ μ₀ α₀ : ℝ) (hβ₀ : 0 < β₀) (hμ₀ : 0 < μ₀) (hα₀ : 0 < α₀) :
    ∃! Λ : ℝ, 0 < Λ ∧ Λ < μ₀ ∧ alphaOneLoop β₀ Λ μ₀ = α₀ := by
  set c : ℝ := 1 / (2 * β₀ * α₀)
  have hden : (2 * β₀ * α₀) ≠ 0 := by positivity
  have hc : 0 < c := by
    have : 0 < 2 * β₀ * α₀ := by positivity
    exact div_pos one_pos this
  set Λ0 : ℝ := μ₀ * exp (-c)
  have hpos : 0 < Λ0 := by positivity
  have hlt : Λ0 < μ₀ := by
    have hexp : exp (-c) < 1 := by
      rw [← exp_zero]
      exact exp_lt_exp.mpr (neg_lt_zero.mpr hc)
    simpa [Λ0, one_mul] using mul_lt_mul_of_pos_left hexp hμ₀
  have h2c : 2 * c = 1 / (β₀ * α₀) := by
    unfold c
    field_simp
  have hlogΛ0 : log Λ0 = log μ₀ - c := by
    have hμne : μ₀ ≠ 0 := hμ₀.ne'
    rw [show Λ0 = μ₀ * exp (-c) from rfl, log_mul hμne (exp_ne_zero _), log_exp]
    ring
  have hlog0 : log (μ₀ ^ 2 / Λ0 ^ 2) = 1 / (β₀ * α₀) := by
    calc
      log (μ₀ ^ 2 / Λ0 ^ 2) = log (μ₀ ^ 2) - log (Λ0 ^ 2) := by
        exact log_div (by positivity) (by positivity)
      _ = 2 * log μ₀ - 2 * log Λ0 := by
        rw [log_pow, log_pow]
        norm_cast
      _ = 2 * log μ₀ - 2 * (log μ₀ - c) := by rw [hlogΛ0]
      _ = 2 * c := by ring
      _ = 1 / (β₀ * α₀) := h2c
  have heq : alphaOneLoop β₀ Λ0 μ₀ = α₀ := by
    unfold alphaOneLoop
    rw [hlog0]
    field_simp
  apply ExistsUnique.intro Λ0
  · exact ⟨hpos, hlt, heq⟩
  · intro Λ ⟨hΛpos, hΛlt, hα⟩
    have hdenΛ : β₀ * log (μ₀ ^ 2 / Λ ^ 2) ≠ 0 := by
      intro hz
      have : alphaOneLoop β₀ Λ μ₀ = 0 := by
        unfold alphaOneLoop
        simp [hz]
      exact hα₀.ne' (hα.symm.trans this)
    have hprod : α₀ * (β₀ * log (μ₀ ^ 2 / Λ ^ 2)) = 1 := by
      have h := hα
      unfold alphaOneLoop at h
      rw [div_eq_iff hdenΛ] at h
      simpa [mul_comm, mul_left_comm, mul_assoc] using h.symm
    have hlog : log (μ₀ ^ 2 / Λ ^ 2) = 1 / (β₀ * α₀) := by
      have hβne : β₀ ≠ 0 := hβ₀.ne'
      have hαne : α₀ ≠ 0 := hα₀.ne'
      field_simp at hprod ⊢
      nlinarith
    have hratio_log : log (μ₀ / Λ) = c := by
      have hquot : 0 < μ₀ / Λ := div_pos hμ₀ hΛpos
      have hsq : μ₀ ^ 2 / Λ ^ 2 = (μ₀ / Λ) ^ 2 := by
        field_simp
      have htwo : log (μ₀ ^ 2 / Λ ^ 2) = 2 * log (μ₀ / Λ) := by
        rw [hsq, log_pow]
        norm_cast
      have : 2 * log (μ₀ / Λ) = 2 * c := by
        rw [← htwo, hlog, h2c]
      linarith
    have hratio : μ₀ / Λ = exp c := by
      rw [← exp_log (div_pos hμ₀ hΛpos), hratio_log]
    have hΛ : Λ = μ₀ * exp (-c) := by
      have hexp : exp c ≠ 0 := exp_ne_zero _
      have hmul : Λ * exp c = μ₀ := by
        calc
          Λ * exp c = Λ * (μ₀ / Λ) := by rw [← hratio]
          _ = μ₀ := by field_simp
      calc
        Λ = (Λ * exp c) * (exp c)⁻¹ := by field_simp
        _ = μ₀ * (exp c)⁻¹ := by rw [hmul]
        _ = μ₀ * exp (-c) := by rw [← exp_neg]
    simpa [Λ0] using hΛ
