-- Prove2me | solution 1 for GDPRPrivacy.PriceRise.eq6_demand_out
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:03:45.268994+00:00
-- url     : https://prove2.me/submissions/a4fbf9bf-e7ca-4eaa-95d1-a41c4b2f06ae

import Mathlib
import Definitions.Def_GDPRPrivacy_PriceRise_Model

set_option autoImplicit false
open MeasureTheory GDPRPrivacy.PriceRise

theorem gdpr_slice (h : ℝ → ℝ) (v : ℝ) :
    volume (Prod.mk v ⁻¹' {q : ℝ × ℝ | q ∈ typeSquare ∧ q.2 ≤ h q.1}) =
      Set.indicator (Set.Icc (0 : ℝ) 1) (fun v => ENNReal.ofReal (min 1 (max 0 (h v)))) v := by
  by_cases hv : v ∈ Set.Icc (0 : ℝ) 1
  · rw [Set.indicator_of_mem hv]
    have : Prod.mk v ⁻¹' {q : ℝ × ℝ | q ∈ typeSquare ∧ q.2 ≤ h q.1} = Set.Icc 0 (min 1 (h v)) := by
      ext c
      simp only [typeSquare, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_prod, Set.mem_Icc, le_min_iff]
      constructor
      · rintro ⟨⟨_, h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
      · rintro ⟨h1, h2, h3⟩; exact ⟨⟨hv, h1, h2⟩, h3⟩
    rw [this, Real.volume_Icc, sub_zero]
    rcases le_total (h v) 0 with h0 | h0
    · rw [min_eq_right (by linarith : h v ≤ 1), max_eq_left h0, min_eq_right zero_le_one,
        ENNReal.ofReal_of_nonpos h0, ENNReal.ofReal_zero]
    · rw [max_eq_right h0]
  · rw [Set.indicator_of_notMem hv]
    have : Prod.mk v ⁻¹' {q : ℝ × ℝ | q ∈ typeSquare ∧ q.2 ≤ h q.1} = ∅ := by
      ext c
      simp only [typeSquare, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_prod, Set.mem_empty_iff_false,
        iff_false, not_and]
      intro h1; exact absurd h1.1 hv
    rw [this]; simp

theorem gdpr_area (h : ℝ → ℝ) (hh : Continuous h) :
    volume {q : ℝ × ℝ | q ∈ typeSquare ∧ q.2 ≤ h q.1} =
      ENNReal.ofReal (∫ v in (0 : ℝ)..1, min 1 (max 0 (h v))) := by
  have hS : MeasurableSet {q : ℝ × ℝ | q ∈ typeSquare ∧ q.2 ≤ h q.1} := by
    have h1 : IsClosed typeSquare := (isClosed_Icc).prod (isClosed_Icc)
    have h2 : IsClosed {q : ℝ × ℝ | q.2 ≤ h q.1} :=
      isClosed_le continuous_snd (hh.comp continuous_fst)
    exact (h1.inter h2).measurableSet
  rw [Measure.volume_eq_prod, Measure.prod_apply hS]
  simp_rw [gdpr_slice]
  rw [lintegral_indicator measurableSet_Icc]
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
  have hc : Continuous fun v => min 1 (max 0 (h v)) := continuous_const.min (continuous_const.max hh)
  rw [ofReal_integral_eq_lintegral_ofReal (hc.integrableOn_Icc)
    (Filter.Eventually.of_forall fun v => le_min zero_le_one (le_max_left _ _))]

theorem gdpr_split {f : ℝ → ℝ} (hf : Continuous f) (a m b : ℝ) :
    ∫ v in a..b, f v = (∫ v in a..m, f v) + ∫ v in m..b, f v :=
  (intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable _ _)
    (hf.intervalIntegrable _ _)).symm

theorem gdpr_piece {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (h : ∀ v ∈ Set.Icc a b, f v = g v) :
    ∫ v in a..b, f v = ∫ v in a..b, g v :=
  intervalIntegral.integral_congr (fun v hv => h v (by rwa [Set.uIcc_of_le hab] at hv))

theorem gdpr_lin (d a b : ℝ) : ∫ v in a..b, (v + d) = (b ^ 2 - a ^ 2) / 2 + d * (b - a) := by
  rw [intervalIntegral.integral_add intervalIntegral.intervalIntegrable_id
    intervalIntegrable_const]
  simp [integral_id]
  ring

theorem gdpr_const (k a b : ℝ) : ∫ _v in a..b, k = k * (b - a) := by
  simp [mul_comm]

theorem solution (x p : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    (1 < p → p < 1 + x → demandOut x p = 0) ∧
    (0 ≤ p → p ≤ 1 → demandOut x p = (1 - x) * (1 - p)) := by
  constructor
  · intro h1 h2
    unfold demandOut
    have : optOutSet x p = ∅ := by
      ext q
      constructor
      · rintro ⟨⟨⟨h3, h4⟩, h5⟩, h6, h7⟩
        exfalso; linarith
      · intro h; exact h.elim
    simp [this]
  · intro h1 h2
    unfold demandOut
    have : optOutSet x p = Set.Icc p 1 ×ˢ Set.Ioc x 1 := by
      ext q
      constructor
      · rintro ⟨⟨⟨h3, h4⟩, h5⟩, h6, h7⟩
        exact ⟨⟨h6, h4⟩, h7, h5.2⟩
      · rintro ⟨⟨h3, h4⟩, h5, h6⟩
        exact ⟨⟨⟨by linarith, h4⟩, by linarith, h6⟩, h3, h5⟩
    rw [this, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Ioc,
      ← ENNReal.ofReal_mul (by linarith), ENNReal.toReal_ofReal (by nlinarith)]
    ring
