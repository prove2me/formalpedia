-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a36_clock_tail_integrability_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T12:25:03.552811+00:00
-- url     : https://prove2.me/submissions/dc620dcb-4c84-4d31-a6d3-2abe268aeabc

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (nu : Measure ℝ) [SFinite nu]
    (g : Ω → ℝ≥0∞) (H : Ω × ℝ → ℝ≥0∞)
    (T : ℝ) (hg : Measurable g)
    (hTail : 0 < nu (Set.Ioi T))
    (hBound : ∀ z : Ω × ℝ, T < z.2 → g z.1 ≤ H z)
    (hMoment : (∫⁻ z : Ω × ℝ, H z ∂ (P.prod nu)) < ⊤) :
    (∫⁻ omega : Ω, g omega ∂ P) < ⊤ := by
  classical
  let F : Ω × ℝ → ℝ≥0∞ := fun z => if T < z.2 then g z.1 else 0
  have hFMeas : Measurable F := by
    exact Measurable.ite (measurableSet_Ioi.preimage measurable_snd)
      (hg.comp measurable_fst) measurable_const
  have hFBound : ∀ z : Ω × ℝ, F z ≤ H z := by
    intro z
    by_cases hz : T < z.2
    · simpa [F, hz] using hBound z hz
    · simp [F, hz]
  have hDom : (∫⁻ z : Ω × ℝ, F z ∂ (P.prod nu)) ≤
      (∫⁻ z : Ω × ℝ, H z ∂ (P.prod nu)) :=
    lintegral_mono hFBound
  have hInner (omega : Ω) :
      (∫⁻ t : ℝ, (if T < t then g omega else 0) ∂ nu) =
        nu (Set.Ioi T) * g omega := by
    calc
      _ = g omega * nu (Set.Ioi T) := by
        simpa only [Set.indicator, Set.mem_Ioi] using
          (lintegral_indicator_const (μ := nu) measurableSet_Ioi (g omega))
      _ = nu (Set.Ioi T) * g omega := mul_comm _ _
  have hEq : (∫⁻ z : Ω × ℝ, F z ∂ (P.prod nu)) =
      nu (Set.Ioi T) * (∫⁻ omega : Ω, g omega ∂ P) := by
    rw [lintegral_prod F hFMeas.aemeasurable]
    change (∫⁻ omega : Ω, ∫⁻ t : ℝ,
      (if T < t then g omega else 0) ∂ nu ∂ P) = _
    simp_rw [hInner]
    exact lintegral_const_mul (nu (Set.Ioi T)) hg
  rw [hEq] at hDom
  have hFin : nu (Set.Ioi T) * (∫⁻ omega : Ω, g omega ∂ P) < ⊤ :=
    lt_of_le_of_lt hDom hMoment
  by_contra hNot
  have hTop : (∫⁻ omega : Ω, g omega ∂ P) = ⊤ :=
    top_unique (le_of_not_gt hNot)
  have hNo : (⊤ : ℝ≥0∞) < ⊤ := by
    simpa [hTop, ENNReal.mul_top, ne_of_gt hTail] using hFin
  exact (lt_irrefl _ hNo)
