-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a534_discounted_positive_endpoint_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:26:08.143199+00:00
-- url     : https://prove2.me/submissions/97350ae0-cffe-4f5d-9f41-7a147493ee18

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (w : ℝ → ℝ) (Z E : Ω → ℝ) (θ K : ℝ)
    (hK : 0 ≤ K) (h0 : w 0 ≤ K)
    (hupper : ∀ y : ℝ, 0 < y → w y ≤ K * Real.exp (θ * y))
    (hZ : ∀ᵐ ω ∂P, 0 ≤ Z ω)
    (hE : ∀ᵐ ω ∂P, 0 ≤ E ω ∧ E ω ≤ 1)
    (hExp : Integrable (fun ω => Real.exp (θ * Z ω)) P)
    (hMeas : AEStronglyMeasurable
      (fun ω => max (E ω * w (Z ω)) (0 : ℝ)) P) :
    Integrable (fun ω => max (E ω * w (Z ω)) (0 : ℝ)) P := by
  have hDom : Integrable (fun ω => K * Real.exp (θ * Z ω)) P :=
    hExp.const_mul K
  apply hDom.mono_nonneg hMeas
    (Filter.Eventually.of_forall fun ω => le_max_right _ _)
  filter_upwards [hZ, hE] with ω hz he
  have hp : 0 ≤ K * Real.exp (θ * Z ω) :=
    mul_nonneg hK (Real.exp_pos _).le
  have hw : w (Z ω) ≤ K * Real.exp (θ * Z ω) := by
    by_cases hzpos : 0 < Z ω
    · exact hupper (Z ω) hzpos
    · have hz0 : Z ω = 0 := le_antisymm (le_of_not_gt hzpos) hz
      simpa [hz0] using h0
  have hew : E ω * w (Z ω) ≤ K * Real.exp (θ * Z ω) := by
    calc
      E ω * w (Z ω) ≤ E ω * (K * Real.exp (θ * Z ω)) :=
        mul_le_mul_of_nonneg_left hw he.1
      _ ≤ K * Real.exp (θ * Z ω) :=
        mul_le_of_le_one_left hp he.2
  have hm : max (E ω * w (Z ω)) (0 : ℝ) ≤
      K * Real.exp (θ * Z ω) := max_le hew hp
  have hnonneg : 0 ≤ max (E ω * w (Z ω)) (0 : ℝ) :=
    le_max_right _ _
  simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hm
