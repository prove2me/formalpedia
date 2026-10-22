-- Prove2me | solution 1 for BatteryLease.WinWin.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:47:24.956992+00:00
-- url     : https://prove2.me/submissions/03f8844f-43f5-4ca9-a501-8b5e04f0d4dd

import Mathlib
import Definitions.Def_BatteryLease_WinWin_Setting

set_option autoImplicit false
open MeasureTheory BatteryLease.WinWin

lemma bl_int_pos (a rh : ℝ) (h0 : 0 ≤ rh) (h1 : rh ≤ a) :
    ∫ D in (0:ℝ)..a, pos (D - rh) = (a - rh) ^ 2 / 2 := by
  have hcont : Continuous (fun D : ℝ => pos (D - rh)) := by
    unfold pos
    exact (continuous_id.sub continuous_const).max continuous_const
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := rh)
    (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  have e1 : ∫ D in (0:ℝ)..rh, pos (D - rh) = ∫ D in (0:ℝ)..rh, (0:ℝ) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le h0] at hx
    simp only [pos]
    exact max_eq_right (by linarith [hx.2])
  have e2 : ∫ D in rh..a, pos (D - rh) = ∫ D in rh..a, (D - rh) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le h1] at hx
    simp only [pos]
    exact max_eq_left (by linarith [hx.1])
  rw [e1, e2]
  have e3 : ∫ D in rh..a, (D - rh) = ∫ D in (rh - rh)..(a - rh), D :=
    intervalIntegral.integral_comp_sub_right (fun x : ℝ => x) rh
  rw [e3]
  simp only [integral_id, intervalIntegral.integral_zero, sub_self]
  ring

theorem solution (a ρ rh ch ph : ℝ) (hS : Standing a ρ rh ch)
    (hτ0 : 0 ≤ (2 * a * ph - (1 - ρ) * rh * (2 * a - rh)) / (2 * a * ρ))
    (hτ1 : (2 * a * ph - (1 - ρ) * rh * (2 * a - rh)) / (2 * a * ρ) ≤ 1)
    (hτr : (2 * a * ph - (1 - ρ) * rh * (2 * a - rh)) / (2 * a * ρ) < rh) :
    (∀ d ∈ Set.Icc (0:ℝ) 1,
      ¬ benchLow a ρ rh ph d ↔ (2 * a * ph - (1 - ρ) * rh * (2 * a - rh)) / (2 * a * ρ) < d) ∧
    tauB a ρ rh ph = (2 * a * ph - (1 - ρ) * rh * (2 * a - rh)) / (2 * a * ρ) ∧
    1 - tauB a ρ rh ph = (2 * a * (ρ - ph) + (1 - ρ) * rh * (2 * a - rh)) / (2 * a * ρ) := by
  obtain ⟨ha1, ⟨hρ0, hρ1⟩, ⟨hrh0, hrha⟩, -⟩ := hS
  have ha0 : 0 < a := by linarith
  have hρpos : 0 < ρ := by
    have : 0 < a / (2 + a) := by positivity
    linarith
  set τ0 := (2 * a * ph - (1 - ρ) * rh * (2 * a - rh)) / (2 * a * ρ) with hτ0def
  have hτ0e : τ0 * (2 * a * ρ) = 2 * a * ph - (1 - ρ) * rh * (2 * a - rh) := by
    rw [hτ0def]; field_simp
  have hEU1 : EU a (fun D => D) = a / 2 := by
    unfold EU
    rw [integral_id]
    field_simp; ring
  have hEU2 : EU a (fun D => pos (D - rh)) = (a - rh) ^ 2 / (2 * a) := by
    unfold EU
    rw [bl_int_pos a rh hrh0.le hrha]
    field_simp
  have key : ∀ d : ℝ, benchLow a ρ rh ph d ↔ d ≤ τ0 := by
    intro d
    unfold benchLow
    rw [hEU1, hEU2]
    simp only [pos]
    have hm : ∀ x : ℝ, (max x 0 = 0 ∧ x ≤ 0) ∨ (max x 0 = x ∧ 0 ≤ x) := by
      intro x
      rcases le_total x 0 with h | h
      · exact Or.inl ⟨max_eq_right h, h⟩
      · exact Or.inr ⟨max_eq_left h, h⟩
    have hA : (a - rh) ^ 2 / (2 * a) = a / 2 - rh * (2 * a - rh) / (2 * a) := by
      field_simp; ring
    rcases hm (d - rh) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, hA]
      have : ρ * d + (1 - ρ) * (a / 2) ≤ ph + ρ * 0 + (1 - ρ) * (a / 2 - rh * (2 * a - rh) / (2 * a)) ↔
          ρ * d ≤ ph - (1 - ρ) * (rh * (2 * a - rh) / (2 * a)) := by
        constructor <;> intro h <;> linarith
      rw [this]
      constructor
      · intro h
        have h' : d * (2 * a * ρ) ≤ τ0 * (2 * a * ρ) := by
          rw [hτ0e]
          have : (1 - ρ) * (rh * (2 * a - rh) / (2 * a)) * (2 * a) =
              (1 - ρ) * rh * (2 * a - rh) := by field_simp
          nlinarith [mul_le_mul_of_nonneg_right h (by positivity : (0:ℝ) ≤ 2 * a)]
        exact le_of_mul_le_mul_right h' (by positivity)
      · intro h
        have h' : d * (2 * a * ρ) ≤ τ0 * (2 * a * ρ) :=
          mul_le_mul_of_nonneg_right h (by positivity)
        rw [hτ0e] at h'
        have : (1 - ρ) * (rh * (2 * a - rh) / (2 * a)) * (2 * a) =
            (1 - ρ) * rh * (2 * a - rh) := by field_simp
        have h'' : ρ * d * (2 * a) ≤ (ph - (1 - ρ) * (rh * (2 * a - rh) / (2 * a))) * (2 * a) := by
          nlinarith
        exact le_of_mul_le_mul_right h'' (by positivity)
    · rw [h1, hA]
      have hfalse : ¬ (ρ * d + (1 - ρ) * (a / 2) ≤
          ph + ρ * (d - rh) + (1 - ρ) * (a / 2 - rh * (2 * a - rh) / (2 * a))) := by
        intro h
        have h2' : ρ * rh ≤ ph - (1 - ρ) * (rh * (2 * a - rh) / (2 * a)) := by linarith
        have h3 : rh * (2 * a * ρ) ≤ τ0 * (2 * a * ρ) := by
          rw [hτ0e]
          have : (1 - ρ) * (rh * (2 * a - rh) / (2 * a)) * (2 * a) =
              (1 - ρ) * rh * (2 * a - rh) := by field_simp
          nlinarith [mul_le_mul_of_nonneg_right h2' (by positivity : (0:ℝ) ≤ 2 * a)]
        have := le_of_mul_le_mul_right h3 (by positivity)
        linarith
      constructor
      · intro h; exact absurd h hfalse
      · intro h; linarith
  have hset : {d : ℝ | d ∈ Set.Icc (0:ℝ) 1 ∧ benchLow a ρ rh ph d} = Set.Icc 0 τ0 := by
    ext d
    simp only [Set.mem_setOf_eq, Set.mem_Icc, key]
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, by linarith⟩, h2⟩
  have htau : tauB a ρ rh ph = τ0 := by
    unfold tauB custVol
    rw [hset, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
    ring
  refine ⟨?_, htau, ?_⟩
  · intro d _
    rw [key]; exact not_le
  · rw [htau, hτ0def]
    field_simp
    ring
