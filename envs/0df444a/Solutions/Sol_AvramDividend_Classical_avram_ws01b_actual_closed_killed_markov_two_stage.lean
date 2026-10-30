-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01b_actual_closed_killed_markov_two_stage
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T08:53:34.522579+00:00
-- url     : https://prove2.me/submissions/8b13697d-b1db-48ab-950a-c80acc22bc73

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_actual_markov_tonelli_killed_history_kernel
import Theorems.Thm_AvramDividend_Classical_shifted_lower_survival_filtration_measurable_no_schedule
import Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_shifted_closed_survival_schedule_iff
import Theorems.Thm_AvramDividend_Classical_scaleFunction_monotone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

/-- Original-Lévy closed killed semigroup factors through its actual
F_s-measurable historical endpoint/survival flag and true future path.
The BV scale origin remains untouched by the historical Boolean mask. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (s u : ℝ≥0) (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (hTerminal : ∃ j : ℕ, τ j = u) :
    let H : Ω → ℝ × Bool := fun ω =>
      (x + X.X s ω,
       if ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω then true else false)
    (∫⁻ ω,
      if ∀ v : ℝ≥0, v ≤ s + u → 0 ≤ x + X.X v ω then
        ENNReal.ofReal (Real.exp (-(q * (u : ℝ))) *
          W (x + X.X (s + u) ω))
      else (0 : ℝ≥0∞) ∂P) =
    ∫⁻ h, ∫⁻ y,
      (if h.2 then
        if ∀ j : ℕ, τ j ≤ u → 0 ≤ h.1 + y (τ j) then
          ENNReal.ofReal (Real.exp (-(q * (u : ℝ))) * W (h.1 + y u))
        else (0 : ℝ≥0∞)
      else (0 : ℝ≥0∞))
      ∂(Measure.map (fun ω => (fun t : ℝ≥0 => X.X t ω)) P)
      ∂(Measure.map H P) := by
  classical
  let A : Set Ω := {ω | ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω}
  let H : Ω → ℝ × Bool := fun ω =>
    (x + X.X s ω, if ω ∈ A then true else false)
  have hA : MeasurableSet[𝓕 s] A := by
    simpa only [A] using
      shifted_lower_survival_filtration_measurable_no_schedule X x s
  have hH : Measurable[𝓕 s] H := by
    dsimp [H]
    exact (measurable_const.add (X.adapted s)).prodMk
      (Measurable.ite hA measurable_const measurable_const)
  have hMeasW : Measurable W :=
    (scaleFunction_monotone X q W hW).measurable
  have hFuture (ω : Ω) :
      (∀ v : ℝ≥0, v ≤ u →
        0 ≤ (x + X.X s ω) + (X.X (s + v) ω - X.X s ω)) ↔
      (∀ j : ℕ, τ j ≤ u →
        0 ≤ (x + X.X s ω) + (X.X (s + τ j) ω - X.X s ω)) := by
    exact chat04_random_reserve_shifted_closed_survival_schedule_iff
      X (fun _ => x + X.X s ω) ω s u τ hCover hTerminal
  have hSplit (ω : Ω) :
      (∀ v : ℝ≥0, v ≤ s + u → 0 ≤ x + X.X v ω) ↔
      (ω ∈ A ∧ ∀ j : ℕ, τ j ≤ u →
        0 ≤ (x + X.X s ω) +
          (X.X (s + τ j) ω - X.X s ω)) := by
    constructor
    · intro hall
      constructor
      · intro v hv
        exact hall v (le_trans hv (le_add_of_nonneg_right zero_le))
      · apply (hFuture ω).mp
        intro v hv
        have h := hall (s + v) (by simpa only [add_comm] using (add_le_add_left hv s))
        linarith
    · rintro ⟨hp, hg⟩ v hv
      rcases le_total v s with hvs | hsv
      · exact hp v hvs
      · obtain ⟨w, rfl⟩ := exists_add_of_le hsv
        have hw : w ≤ u := (add_le_add_iff_left s).mp hv
        have h := (hFuture ω).mpr hg w hw
        linarith
  have hPoint (ω : Ω) :
      (if ∀ v : ℝ≥0, v ≤ s + u → 0 ≤ x + X.X v ω then
        ENNReal.ofReal (Real.exp (-(q * (u : ℝ))) *
          W (x + X.X (s + u) ω))
      else (0 : ℝ≥0∞)) =
      (if (H ω).2 then
        if ∀ j : ℕ, τ j ≤ u →
          0 ≤ (H ω).1 + (X.X (s + τ j) ω - X.X s ω) then
          ENNReal.ofReal (Real.exp (-(q * (u : ℝ))) *
            W ((H ω).1 + (X.X (s + u) ω - X.X s ω)))
        else (0 : ℝ≥0∞)
      else (0 : ℝ≥0∞)) := by
    by_cases hp : ω ∈ A
    · have hEq : (∀ v : ℝ≥0, v ≤ s + u →
          0 ≤ x + X.X v ω) ↔
        (∀ j : ℕ, τ j ≤ u →
          0 ≤ (x + X.X s ω) +
            (X.X (s + τ j) ω - X.X s ω)) := by
          simpa only [hp, true_and] using hSplit ω
      by_cases hg : ∀ j : ℕ, τ j ≤ u →
          0 ≤ (x + X.X s ω) +
            (X.X (s + τ j) ω - X.X s ω)
      · have hf := hEq.mpr hg
        have hterm : (x + X.X s ω) +
            (X.X (s + u) ω - X.X s ω) = x + X.X (s + u) ω := by ring
        simp only [if_pos hf]
        dsimp only [H, Prod.snd, Prod.fst]
        simp only [if_pos hp, ite_true, if_pos hg, hterm]
      · have hf : ¬ (∀ v : ℝ≥0, v ≤ s + u →
          0 ≤ x + X.X v ω) := fun h => hg (hEq.mp h)
        have hg' : ¬ (∀ j : ℕ, τ j ≤ u →
            0 ≤ x + X.X (s + τ j) ω) := by
          intro hh
          apply hg
          intro j hj
          have hz := hh j hj
          linarith
        simp [hf, H, hp, hg']
    · have hf : ¬ (∀ v : ℝ≥0, v ≤ s + u →
        0 ≤ x + X.X v ω) := fun h => hp (((hSplit ω).mp h).1)
      simp [hf, H, hp]
  have hMark :=
    avram_ws01b_actual_markov_tonelli_killed_history_kernel
      X s H hH τ u q W hMeasW
  change (∫⁻ ω,
      if ∀ v : ℝ≥0, v ≤ s + u → 0 ≤ x + X.X v ω then
        ENNReal.ofReal (Real.exp (-(q * (u : ℝ))) *
          W (x + X.X (s + u) ω))
      else (0 : ℝ≥0∞) ∂P) = _
  calc
    _ = ∫⁻ ω,
      (if (H ω).2 then
        if ∀ j : ℕ, τ j ≤ u →
          0 ≤ (H ω).1 + (X.X (s + τ j) ω - X.X s ω) then
          ENNReal.ofReal (Real.exp (-(q * (u : ℝ))) *
            W ((H ω).1 + (X.X (s + u) ω - X.X s ω)))
        else (0 : ℝ≥0∞)
      else (0 : ℝ≥0∞)) ∂P := lintegral_congr_ae (Filter.Eventually.of_forall hPoint)
    _ = _ := hMark