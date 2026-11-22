-- Prove2me | solution 1 for AvramDividend.Classical.negative_levy_tail_real_integral_bridge_corrected
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T12:15:01.71206+00:00
-- url     : https://prove2.me/submissions/86e58c66-fb5f-480d-be35-167c904a8fe9

/-
Correct the source-fidelity placement of the outer Lévy measure and
combine proved Avram primitive-integrability, finite-tail, and Tonelli lemmas.
-/
import Mathlib
import Theorems.Thm_AvramDividend_Classical_negative_levy_compensated_primitive_integrable
import Theorems.Thm_AvramDividend_Classical_negative_levy_tail_finite_of_quadratic
import Theorems.Thm_AvramDividend_Classical_negative_levy_real_tail_tonelli_outer_measure

open MeasureTheory Set
open scoped NNReal ENNReal

noncomputable section

theorem solution
    (ν : Measure ℝ) (hSupp : ν (Ici (0 : ℝ)) = 0)
    (hQuad : (∫⁻ y : ℝ, ENNReal.ofReal (min 1 (y ^ 2)) ∂ν) < ⊤)
    (hLarge : IntegrableOn (fun y : ℝ => y) (Iic (-1 : ℝ)) ν)
    (θ : ℝ) (hθ : 0 < θ) :
    Integrable (fun y : ℝ => ∫ t in (0 : ℝ)..(-y), 1 - Real.exp (-θ * t)) ν ∧
    IntegrableOn (fun t : ℝ => (1 - Real.exp (-θ * t)) *
      (ν (Iio (-t))).toReal) (Ioi (0 : ℝ)) ∧
    (∫ y : ℝ, (∫ t in (0 : ℝ)..(-y), 1 - Real.exp (-θ * t)) ∂ν) =
    (∫ t in Ioi (0 : ℝ),
      (1 - Real.exp (-θ * t)) * (ν (Iio (-t))).toReal) := by
  have hI :=
    AvramDividend.Classical.negative_levy_compensated_primitive_integrable
      ν hSupp hQuad hLarge θ hθ
  have hF :=
    AvramDividend.Classical.negative_levy_tail_finite_of_quadratic ν hQuad
  obtain ⟨hO, hEq⟩ :=
    AvramDividend.Classical.negative_levy_real_tail_tonelli_outer_measure
      ν hSupp hF θ hθ hI
  exact ⟨hI, hO, hEq⟩
