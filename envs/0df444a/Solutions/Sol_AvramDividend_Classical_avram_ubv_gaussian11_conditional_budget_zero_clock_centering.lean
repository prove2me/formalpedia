-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gaussian11_conditional_budget_zero_clock_centering
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T14:39:58.314552+00:00
-- url     : https://prove2.me/submissions/0210f812-7ce6-45ed-a2df-83c2315f1fe6

import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (A : Set Ω) (hA : MeasurableSet A)
    (hApos : 0 < (P A).toReal)
    (F : Ω → ℝ) (hFI : Integrable F P) (b : ℝ)
    (hbudget : (∫ ω in A, F ω ∂P) ≤ b * (P A).toReal) :
    ∃ M : Ω → ℝ,
      Integrable M P ∧
      (∫ ω, M ω ∂P) = 0 ∧
      (∀ ω, ω ∉ A → M ω = 0) ∧
      (∀ ω, ω ∈ A → F ω ≤ b + M ω) := by
  classical
  let a : ℝ := (P A).toReal
  let μ : ℝ := ∫ ω in A, F ω ∂P
  let m : ℝ := μ / a
  let M : Ω → ℝ := fun ω => if ω ∈ A then F ω - m else 0
  have hm : m ≤ b := by
    dsimp [m, μ, a]
    apply (div_le_iff₀ hApos).2
    simpa [mul_comm] using hbudget
  have hMint : Integrable M P := by
    change Integrable (A.indicator (F - fun _ => m)) P
    exact (hFI.sub (integrable_const m)).indicator hA
  have hFA : Integrable F (P.restrict A) := hFI.integrableOn
  refine ⟨M, hMint, ?_, ?_, ?_⟩
  · have hMeq : (∫ ω, M ω ∂P) = ∫ ω in A, F ω - m ∂P := by
      simpa only [M, Set.indicator, Pi.sub_apply] using
        (MeasureTheory.integral_indicator
          (f := fun ω => F ω - m) (s := A) (μ := P) hA)
    rw [hMeq, integral_sub hFA (integrable_const m)]
    simp only [integral_const, smul_eq_mul]
    have ha_restrict : (P.restrict A).real Set.univ = a := by
      simp [a, Measure.real]
    rw [ha_restrict]
    change μ - a * (μ / a) = 0
    have ha : a ≠ 0 := ne_of_gt hApos
    field_simp [ha] <;> ring
  · intro ω hω
    simp [M, hω]
  · intro ω hω
    simp only [M, if_pos hω]
    linarith
