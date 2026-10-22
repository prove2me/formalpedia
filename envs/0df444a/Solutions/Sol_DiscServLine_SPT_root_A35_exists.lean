-- Prove2me | solution 1 for DiscServLine.SPT.root_A35_exists
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T06:58:24.6627+00:00
-- url     : https://prove2.me/submissions/2c222d42-8cb1-49f2-a743-ea472b7b4d89

import Mathlib
import Definitions.Def_DiscServLine_SPT_Model

open DiscServLine.SPT

theorem solution (P : Params) (hP : P.Standing) :
    ∃ ω ∈ Set.Ioo (0 : ℝ) 1, F35 P ω = 0 := by
  obtain ⟨hc, hcθ, hb, hΛ⟩ := hP
  have hκ : 0 < κ P := by unfold κ; positivity
  set m := P.θbar / P.c - 1 with hm
  have hm0 : 0 < m := by rw [hm, sub_pos, one_lt_div hc]; exact hcθ
  set D := P.b / (P.Λ * P.c) + 1 + Real.sqrt (1 + κ P) with hD
  have hs1 : 1 ≤ Real.sqrt (1 + κ P) := by
    have := Real.sqrt_le_sqrt (show (1:ℝ) ≤ 1 + κ P by linarith); simpa using this
  have hD2 : 2 ≤ D := by
    have : 0 ≤ P.b / (P.Λ * P.c) := by positivity
    linarith
  set ω0 := Real.exp (-(2 * m + 2)) / D with hω0
  have hω0pos : 0 < ω0 := by positivity
  have hω0lt : ω0 < 1 := by
    rw [hω0, div_lt_one (by linarith)]
    have : Real.exp (-(2 * m + 2)) < 1 := by rw [Real.exp_lt_one_iff]; linarith
    linarith
  -- continuity on [ω0, 1]
  have hcont : ContinuousOn (F35 P) (Set.Icc ω0 1) := by
    have hpos : ∀ x ∈ Set.Icc ω0 1, 0 < x := fun x hx => lt_of_lt_of_le hω0pos hx.1
    have hinner : ∀ x ∈ Set.Icc ω0 1, 0 < 1 / x + κ P := fun x hx => by
      have := hpos x hx; positivity
    unfold F35
    apply ContinuousOn.add
    apply ContinuousOn.sub
    · apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.log
      · apply ContinuousOn.div_const
        apply ContinuousOn.add
        · apply ContinuousOn.add continuousOn_const
          exact continuousOn_const.div continuousOn_id (fun x hx => (hpos x hx).ne')
        · apply ContinuousOn.mul
          · exact continuousOn_const.div (Real.continuous_sqrt.comp_continuousOn continuousOn_id)
              (fun x hx => (Real.sqrt_pos.mpr (hpos x hx)).ne')
          · apply Real.continuous_sqrt.comp_continuousOn
            exact (continuousOn_const.div continuousOn_id (fun x hx => (hpos x hx).ne')).add
              continuousOn_const
      · intro x hx
        have := hpos x hx
        have : 0 < D := by linarith
        apply ne_of_gt; apply div_pos _ this
        positivity
    · apply continuousOn_const.div
      · apply Real.continuous_sqrt.comp_continuousOn
        exact (continuousOn_const.div continuousOn_id (fun x hx => (hpos x hx).ne')).add
          continuousOn_const
      · intro x hx; exact (Real.sqrt_pos.mpr (hinner x hx)).ne'
    · exact continuousOn_const.sub (Real.continuous_sqrt.comp_continuousOn
        (continuousOn_const.add (continuousOn_const.mul continuousOn_id)))
  -- value at 1
  have hF1 : F35 P 1 < 0 := by
    unfold F35
    simp only [div_one, Real.sqrt_one, one_div_one, one_mul, mul_one]
    rw [← hD, div_self (by linarith), Real.log_one, mul_zero, zero_sub, sub_self, add_zero,
      neg_lt_zero, ← hm]
    positivity
  -- value at ω0
  have hF0 : 0 < F35 P ω0 := by
    unfold F35
    rw [← hD, ← hm]
    have hN : 1 / ω0 ≤ P.b / (P.Λ * P.c) + 1 / ω0 +
        1 / Real.sqrt ω0 * Real.sqrt (1 / ω0 + κ P) := by
      have : 0 ≤ P.b / (P.Λ * P.c) := by positivity
      have : 0 ≤ 1 / Real.sqrt ω0 * Real.sqrt (1 / ω0 + κ P) := by positivity
      linarith
    have hDpos : 0 < D := by linarith
    have hlog : 2 * m + 2 ≤ Real.log ((P.b / (P.Λ * P.c) + 1 / ω0 +
        1 / Real.sqrt ω0 * Real.sqrt (1 / ω0 + κ P)) / D) := by
      have h1 : Real.log (1 / ω0 / D) = 2 * m + 2 := by
        rw [hω0]; field_simp
        rw [one_div, Real.log_inv, Real.log_exp]; ring
      rw [← h1]
      apply Real.log_le_log (by positivity)
      exact div_le_div_of_nonneg_right hN hDpos.le
    have hsq : 1 ≤ Real.sqrt (1 / ω0 + κ P) := by
      have : 1 ≤ 1 / ω0 := by rw [le_div_iff₀ hω0pos]; linarith
      have := Real.sqrt_le_sqrt (show (1:ℝ) ≤ 1 / ω0 + κ P by linarith); simpa using this
    have h2 : m / Real.sqrt (1 / ω0 + κ P) ≤ m := div_le_self hm0.le hsq
    have h3 : Real.sqrt (1 + κ P * ω0) ≤ Real.sqrt (1 + κ P) := by
      apply Real.sqrt_le_sqrt; nlinarith
    nlinarith
  obtain ⟨ω, hωmem, hωF⟩ := intermediate_value_Icc' hω0lt.le hcont ⟨hF1.le, hF0.le⟩
  refine ⟨ω, ⟨lt_of_lt_of_le hω0pos hωmem.1, lt_of_le_of_ne hωmem.2 ?_⟩, hωF⟩
  rintro rfl; linarith
