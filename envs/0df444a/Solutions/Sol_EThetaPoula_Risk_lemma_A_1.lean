-- Prove2me | solution 1 for EThetaPoula.Risk.lemma_A_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T00:12:01.604333+00:00
-- url     : https://prove2.me/submissions/4c63d50b-72e8-428d-bb8a-a3a5781dfbc8

import Mathlib
import Definitions.Def_EThetaPoula_Risk_Model
open MeasureTheory ProbabilityTheory
open scoped NNReal

open EThetaPoula.Risk in
theorem solution {d m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (S : Model d m Ω)
    (C : AssumptionData d m) (h3 : S.Assumption3 C) (ε : ℝ) (hε : ε ∈ Set.Ioo (0 : ℝ) 1)
    (lam : ℝ) (hlam : 0 < lam) (hlam1 : lam ≤ 1) (θ : Eucl d) (x : Eucl m) (i : Fin d) :
    |S.Glam lam ε θ x i| ≤ 2 * lam ^ (-(1 / 2 : ℝ)) ∧
    |S.Flam lam θ x i| ≤ lam ^ (-(1 / 2 : ℝ)) * (1 + ‖x‖) ^ S.ρ * (C.KF + C.KF * |θ i|) := by
  have hs : 0 < √lam := Real.sqrt_pos.mpr hlam
  have hs1 : √lam ≤ 1 := Real.sqrt_le_one.mpr hlam1
  have hpow : lam ^ (-(1 / 2 : ℝ)) = (√lam)⁻¹ := by
    rw [Real.rpow_neg hlam.le, Real.sqrt_eq_rpow]
  have hinv1 : 1 ≤ (√lam)⁻¹ := by
    rw [le_inv_comm₀ one_pos hs, inv_one]; exact hs1
  have hε0 := hε.1
  rw [hpow]
  change |S.G θ x i / (1 + √lam * |S.G θ x i|) * (1 + √lam / (ε + |S.G θ x i|))| ≤ 2 * (√lam)⁻¹ ∧
    |S.F θ x i / (1 + √lam * ‖θ‖ ^ (2 * S.r))| ≤ (√lam)⁻¹ * (1 + ‖x‖) ^ S.ρ * (C.KF + C.KF * |θ i|)
  obtain ⟨s, hsd⟩ : ∃ s, s = √lam := ⟨_, rfl⟩
  rw [← hsd]
  rw [← hsd] at hs hs1 hinv1
  constructor
  · obtain ⟨a, had⟩ : ∃ a, a = |S.G θ x i| := ⟨_, rfl⟩
    have ha : 0 ≤ a := by rw [had]; exact abs_nonneg _
    have h1pos : 0 < 1 + s * a := by nlinarith
    have h2pos : 0 < ε + a := by linarith
    have h3pos : 0 < 1 + s / (ε + a) := by
      have := div_nonneg hs.le h2pos.le; linarith
    rw [abs_mul, abs_div, ← had, abs_of_pos h1pos, abs_of_pos h3pos]
    have hu1 : a / (1 + s * a) ≤ s⁻¹ := by
      rw [div_le_iff₀ h1pos]
      have : s⁻¹ * (1 + s * a) = s⁻¹ + a := by field_simp
      rw [this]
      have : 0 < s⁻¹ := inv_pos.mpr hs
      linarith
    have hu2 : a / (1 + s * a) ≤ a := div_le_self ha (by nlinarith)
    have hv : s / (ε + a) * a ≤ s := by
      rw [div_mul_eq_mul_div, div_le_iff₀ h2pos]
      nlinarith
    have hsinv : s ≤ s⁻¹ := le_trans hs1 hinv1
    calc a / (1 + s * a) * (1 + s / (ε + a))
        = a / (1 + s * a) + s / (ε + a) * (a / (1 + s * a)) := by ring
      _ ≤ s⁻¹ + s / (ε + a) * a :=
          add_le_add hu1 (mul_le_mul_of_nonneg_left hu2 (div_nonneg hs.le h2pos.le))
      _ ≤ 2 * s⁻¹ := by linarith
  · have hF := h3.2.2.2 θ x i
    have hKF := h3.2.2.1
    obtain ⟨t, htd⟩ : ∃ t, t = ‖θ‖ ^ (2 * S.r) := ⟨_, rfl⟩
    rw [← htd] at hF ⊢
    have ht : 0 ≤ t := by rw [htd]; positivity
    have hX : 0 ≤ (1 + ‖x‖) ^ S.ρ := Real.rpow_nonneg (by positivity) _
    have hpos : 0 < 1 + s * t := by nlinarith
    rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    have key : 1 + t ≤ s⁻¹ * (1 + s * t) := by
      rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul, mul_one]
      linarith
    have hnn : 0 ≤ C.KF * (1 + ‖x‖) ^ S.ρ * (1 + |θ i|) :=
      mul_nonneg (mul_nonneg hKF.le hX) (by positivity)
    calc |S.F θ x i| ≤ C.KF * (1 + ‖x‖) ^ S.ρ * (1 + |θ i|) * (1 + t) := hF
      _ ≤ C.KF * (1 + ‖x‖) ^ S.ρ * (1 + |θ i|) * (s⁻¹ * (1 + s * t)) :=
          mul_le_mul_of_nonneg_left key hnn
      _ = s⁻¹ * (1 + ‖x‖) ^ S.ρ * (C.KF + C.KF * |θ i|) * (1 + s * t) := by ring
