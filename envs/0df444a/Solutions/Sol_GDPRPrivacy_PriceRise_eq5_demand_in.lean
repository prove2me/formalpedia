-- Prove2me | solution 1 for GDPRPrivacy.PriceRise.eq5_demand_in
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:04:23.088547+00:00
-- url     : https://prove2.me/submissions/712cef89-1868-48dc-9192-4d139612c85a

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
    (1 < p → p < 1 + x → demandIn x p = (1 + x - p) ^ 2 / 2) ∧
    (x < p → p ≤ 1 → demandIn x p = x ^ 2 / 2 + x * (1 - p)) ∧
    (0 ≤ p → p ≤ x → demandIn x p = x - p ^ 2 / 2) := by
  have hb : optInSet x p =
      {q : ℝ × ℝ | q ∈ typeSquare ∧ q.2 ≤ (fun v => min (v + x - p) x) q.1} := by
    ext q
    simp only [optInSet, Set.mem_setOf_eq, le_min_iff]
  have key : demandIn x p = ∫ v in (0 : ℝ)..1, min 1 (max 0 (min (v + x - p) x)) := by
    unfold demandIn
    rw [hb, gdpr_area (fun v => min (v + x - p) x) (by fun_prop), ENNReal.toReal_ofReal]
    exact intervalIntegral.integral_nonneg zero_le_one
      (fun v _ => le_min zero_le_one (le_max_left _ _))
  set f : ℝ → ℝ := fun v => min 1 (max 0 (min (v + x - p) x)) with hf
  have hfc : Continuous f := by fun_prop
  rw [key]
  refine ⟨?_, ?_, ?_⟩
  · intro h1 h2
    rw [gdpr_split hfc 0 (p - x) 1]
    have e1 : ∫ v in (0 : ℝ)..(p - x), f v = 0 := by
      rw [gdpr_piece (g := fun _ => (0 : ℝ)) (by linarith)
        (by intro v hv; simp only [hf, min_def, max_def]; split_ifs <;> linarith [hv.1, hv.2])]
      simp
    have e2 : ∫ v in (p - x)..1, f v = ((1 : ℝ) ^ 2 - (p - x) ^ 2) / 2 + (x - p) * (1 - (p - x)) := by
      rw [gdpr_piece (g := fun v => v + (x - p)) (by linarith)
        (by intro v hv; simp only [hf, min_def, max_def]; split_ifs <;> linarith [hv.1, hv.2]),
        gdpr_lin]
    rw [e1, e2]; ring
  · intro h1 h2
    rw [gdpr_split hfc 0 p 1, gdpr_split hfc 0 (p - x) p]
    have e1 : ∫ v in (0 : ℝ)..(p - x), f v = 0 := by
      rw [gdpr_piece (g := fun _ => (0 : ℝ)) (by linarith)
        (by intro v hv; simp only [hf, min_def, max_def]; split_ifs <;> linarith [hv.1, hv.2])]
      simp
    have e2 : ∫ v in (p - x)..p, f v = (p ^ 2 - (p - x) ^ 2) / 2 + (x - p) * (p - (p - x)) := by
      rw [gdpr_piece (g := fun v => v + (x - p)) (by linarith)
        (by intro v hv; simp only [hf, min_def, max_def]; split_ifs <;> linarith [hv.1, hv.2]),
        gdpr_lin]
    have e3 : ∫ v in p..1, f v = x * (1 - p) := by
      rw [gdpr_piece (g := fun _ => x) (by linarith)
        (by intro v hv; simp only [hf, min_def, max_def]; split_ifs <;> linarith [hv.1, hv.2]),
        gdpr_const]
    rw [e1, e2, e3]; ring
  · intro h1 h2
    rw [gdpr_split hfc 0 p 1]
    have e1 : ∫ v in (0 : ℝ)..p, f v = (p ^ 2 - 0 ^ 2) / 2 + (x - p) * (p - 0) := by
      rw [gdpr_piece (g := fun v => v + (x - p)) (by linarith)
        (by intro v hv; simp only [hf, min_def, max_def]; split_ifs <;> linarith [hv.1, hv.2]),
        gdpr_lin]
    have e3 : ∫ v in p..1, f v = x * (1 - p) := by
      rw [gdpr_piece (g := fun _ => x) (by linarith)
        (by intro v hv; simp only [hf, min_def, max_def]; split_ifs <;> linarith [hv.1, hv.2]),
        gdpr_const]
    rw [e1, e3]; ring
