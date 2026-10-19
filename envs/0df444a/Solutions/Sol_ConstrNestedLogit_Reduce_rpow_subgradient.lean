-- Prove2me | solution 1 for ConstrNestedLogit.Reduce.rpow_subgradient
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T07:24:20.566898+00:00
-- url     : https://prove2.me/submissions/a75a6944-b6fc-4781-908c-69a23fd96397

import Mathlib
set_option autoImplicit false

theorem solution (γ α : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hα : 1 ≤ α)
    (u û : ℝ) (hu : 0 ≤ u) (hû : 0 < û) :
    u ^ γ ≤ û ^ γ + γ * û ^ (γ - 1) * (u - û) ∧
    û ^ γ + γ * û ^ (γ - 1) * (u - û) = û ^ (γ - 1) * (γ * u + (1 - γ) * û) ∧
    û ^ (γ - 1) * (γ * u + (1 - γ) * û) ≤ û ^ (γ - 1) * (γ * u + α * (1 - γ) * û) := by
  have hpow : û ^ γ = û ^ (γ - 1) * û := by
    rw [Real.rpow_sub_one hû.ne']; field_simp
  have hnn : 0 ≤ û ^ (γ - 1) := Real.rpow_nonneg hû.le _
  refine ⟨?_, ?_, ?_⟩
  · have hs : (-1 : ℝ) ≤ u / û - 1 := by
      have : 0 ≤ u / û := div_nonneg hu hû.le
      linarith
    have hb := rpow_one_add_le_one_add_mul_self hs hγ0.le hγ1
    have e : (1 : ℝ) + (u / û - 1) = u / û := by ring
    rw [e, Real.div_rpow hu hû.le] at hb
    have hpos : 0 < û ^ γ := Real.rpow_pos_of_pos hû _
    have h2 : u ^ γ ≤ û ^ γ * (1 + γ * (u / û - 1)) := by
      calc u ^ γ = û ^ γ * (u ^ γ / û ^ γ) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hb hpos.le
    have h3 : û ^ γ * (1 + γ * (u / û - 1)) = û ^ γ + γ * û ^ (γ - 1) * (u - û) := by
      rw [hpow]; field_simp
    linarith
  · rw [hpow]; ring
  · apply mul_le_mul_of_nonneg_left _ hnn
    have : 0 ≤ (1 - γ) * û := mul_nonneg (by linarith) hû.le
    nlinarith
