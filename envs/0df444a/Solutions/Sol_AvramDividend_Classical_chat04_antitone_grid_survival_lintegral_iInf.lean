-- Prove2me | solution 1 for AvramDividend.Classical.chat04_antitone_grid_survival_lintegral_iInf
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T07:33:11.823019+00:00
-- url     : https://prove2.me/submissions/10e813b5-6ae8-4e37-b589-e4da79ec4eff

import Mathlib.MeasureTheory.Integral.Lebesgue.Sub

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-!
Nonnegative payoff expected on progressively finer decreasing grid-survival
events converges to the intersection-event expected payoff. This is an exact
lintegral iInf identity under a finite un-killed payoff moment.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (A : ℕ → Set Ω) (hA : ∀ n, MeasurableSet (A n))
    (hAnti : Antitone A)
    (g : Ω → ℝ≥0∞) (hg : Measurable g)
    (hFin : (∫⁻ ω, g ω ∂P) ≠ ∞) :
    (∫⁻ ω, (⋂ n, A n).indicator g ω ∂P) =
      ⨅ n, ∫⁻ ω, (A n).indicator g ω ∂P := by
  let f : ℕ → Ω → ℝ≥0∞ := fun n => (A n).indicator g
  have hMeas : ∀ n, Measurable (f n) := by
    intro n
    exact hg.indicator (hA n)
  have hFnAnti : Antitone f := by
    intro n m hnm ω
    by_cases hm : ω ∈ A m
    · have hn : ω ∈ A n := (hAnti hnm) hm
      simp [f, Set.indicator, hm, hn]
    · simp [f, Set.indicator, hm]
  have hLe : (∫⁻ ω, f 0 ω ∂P) ≤ ∫⁻ ω, g ω ∂P := by
    apply lintegral_mono
    intro ω
    by_cases hw : ω ∈ A 0
    · simp [f, Set.indicator, hw]
    · simp [f, Set.indicator, hw]
  have hFin0 : (∫⁻ ω, f 0 ω ∂P) ≠ ∞ :=
    ne_top_of_le_ne_top hFin hLe
  have hPoint (ω : Ω) :
      (⋂ n, A n).indicator g ω = ⨅ n, f n ω := by
    by_cases hw : ω ∈ ⋂ n, A n
    · have hn : ∀ n, ω ∈ A n := Set.mem_iInter.mp hw
      simp [Set.indicator, f, hw, hn]
    · have hn : ∃ n, ω ∉ A n := by
        by_contra hnone
        have hAll : ∀ n, ω ∈ A n := by
          intro n
          by_contra hn
          exact hnone ⟨n, hn⟩
        exact hw (Set.mem_iInter.mpr hAll)
      obtain ⟨n, hn⟩ := hn
      have hzero : f n ω = 0 := by
        simp [f, Set.indicator, hn]
      have hle : (⨅ k, f k ω) ≤ 0 := by
        calc
          (⨅ k, f k ω) ≤ f n ω := iInf_le (fun k => f k ω) n
          _ = 0 := hzero
      have heq : (⨅ k, f k ω) = 0 :=
        le_antisymm hle bot_le
      simp [Set.indicator, hw, heq]
  calc
    (∫⁻ ω, (⋂ n, A n).indicator g ω ∂P) =
        ∫⁻ ω, ⨅ n, f n ω ∂P := by
          apply lintegral_congr
          intro ω
          exact hPoint ω
    _ = ⨅ n, ∫⁻ ω, f n ω ∂P :=
      MeasureTheory.lintegral_iInf hMeas hFnAnti hFin0
    _ = ⨅ n, ∫⁻ ω, (A n).indicator g ω ∂P := rfl
