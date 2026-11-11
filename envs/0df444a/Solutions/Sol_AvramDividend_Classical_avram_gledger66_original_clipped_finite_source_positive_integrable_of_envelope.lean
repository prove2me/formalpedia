-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger66_original_clipped_finite_source_positive_integrable_of_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T01:00:54.415895+00:00
-- url     : https://prove2.me/submissions/7686cc4c-59c1-432b-a1e3-4cc81fc485aa

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger59_clipped_finite_source_one_sided_upper_sum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
noncomputable section

/-- A source-exact finite Gaussian stopped mesh is positive-part integrable
    once its active cells have a lower value floor and exponential terminal
    envelope. The negative source tail need not be integrable. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P]
    (m : ℕ) (E Y Z : ℕ → Ω → ℝ) (w : ℝ → ℝ)
    (θ K b : ℝ) (hK : 0 ≤ K) (hb : 0 ≤ b)
    (hSmeas : AEMeasurable
      (fun ω => Finset.sum (Finset.range (m + 1)) (fun i =>
        (E (i + 1) ω - E i ω) * w (Y i ω) +
        E (i + 1) ω * (w (Z i ω) - w (Y i ω)))) P)
    (hE0 : ∀ ω i, 0 ≤ E i ω)
    (hE1 : ∀ ω i, E i ω ≤ 1)
    (hcell : ∀ᵐ ω ∂P, ∀ i ∈ Finset.range (m + 1),
      (E (i + 1) ω = E i ω ∧ Z i ω = Y i ω) ∨
      (-b ≤ w (Y i ω) ∧
        w (Z i ω) ≤ K * Real.exp (θ * Z i ω)))
    (hexp : ∀ i ∈ Finset.range (m + 1),
      Integrable (fun ω => Real.exp (θ * Z i ω)) P) :
    Integrable (fun ω => max
      (Finset.sum (Finset.range (m + 1)) (fun i =>
        (E (i + 1) ω - E i ω) * w (Y i ω) +
        E (i + 1) ω * (w (Z i ω) - w (Y i ω)))) 0) P := by
  let S : Ω → ℝ := fun ω => Finset.sum (Finset.range (m + 1)) (fun i =>
    (E (i + 1) ω - E i ω) * w (Y i ω) +
    E (i + 1) ω * (w (Z i ω) - w (Y i ω)))
  let T : Ω → ℝ := fun ω => Finset.sum (Finset.range (m + 1)) (fun i =>
    K * Real.exp (θ * Z i ω) + b)
  have hT : Integrable T P := by
    dsimp [T]
    apply integrable_finset_sum
    intro i hi
    exact ((hexp i hi).const_mul K).add (integrable_const b)
  have hbound : ∀ᵐ ω ∂P, S ω ≤ T ω := by
    filter_upwards [hcell] with ω hω
    exact avram_gledger59_clipped_finite_source_one_sided_upper_sum
      m (fun i => E i ω) (fun i => Y i ω) (fun i => Z i ω)
      w θ K b hK hb (hE0 ω) (hE1 ω) (hω)
  have hTnonneg : ∀ᵐ ω ∂P, 0 ≤ T ω := by
    apply Filter.Eventually.of_forall
    intro ω
    dsimp [T]
    apply Finset.sum_nonneg
    intro i hi
    positivity
  have hSmaxmeas : AEStronglyMeasurable (fun ω => max (S ω) 0) P :=
    (hSmeas.max aemeasurable_const).aestronglyMeasurable
  have hSmaxnonneg : ∀ᵐ ω ∂P, 0 ≤ max (S ω) 0 :=
    Filter.Eventually.of_forall (fun ω => le_max_right _ _)
  have hSmaxle : ∀ᵐ ω ∂P, max (S ω) 0 ≤ T ω := by
    filter_upwards [hbound, hTnonneg] with ω hω hω0
    exact max_le hω hω0
  exact hT.mono_nonneg hSmaxmeas hSmaxnonneg hSmaxle
