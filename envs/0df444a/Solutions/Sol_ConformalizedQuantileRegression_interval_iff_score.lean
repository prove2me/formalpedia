-- Prove2me | solution 1 for ConformalizedQuantileRegression.interval_iff_score
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-24T21:02:26.846526+00:00
-- url     : https://prove2.me/submissions/c3cd264c-54af-4e26-9bed-290a7f24a22a

import Mathlib
import Definitions.Def_ConformalizedQuantileRegression_Basic

open MeasureTheory ProbabilityTheory
namespace ConformalizedQuantileRegression

theorem interval_iff_score {p n : ℕ} {I₁ : Finset (Fin n)} (A : QRAlgorithm p I₁)
    (I₂ : Finset (Fin n)) (α : ℝ) (d : Fin n → Sample p) (z : Sample p) :
    z.2 ∈ cqrInterval A I₂ α d z.1 ↔
      (conformityScore (fitQR A d).1 (fitQR A d).2 z : EReal) ≤ cqrCorrection A I₂ α d := by
  simp only [cqrInterval, Set.mem_setOf_eq, conformityScore]
  generalize cqrCorrection A I₂ α d = Q
  induction Q using EReal.rec with
  | bot => simp
  | top => simp
  | coe q =>
    rw [← EReal.coe_sub, ← EReal.coe_add, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff,
      EReal.coe_le_coe_iff, max_le_iff]
    constructor
    · rintro ⟨h1, h2⟩; constructor <;> linarith
    · rintro ⟨h1, h2⟩; constructor <;> linarith

end ConformalizedQuantileRegression

open ConformalizedQuantileRegression in
theorem solution {p n : ℕ} {I₁ : Finset (Fin n)} (A : QRAlgorithm p I₁)
    (I₂ : Finset (Fin n)) (α : ℝ) (d : Fin n → Sample p) (z : Sample p) :
    z.2 ∈ cqrInterval A I₂ α d z.1 ↔
      (conformityScore (fitQR A d).1 (fitQR A d).2 z : EReal) ≤ cqrCorrection A I₂ α d :=
  ConformalizedQuantileRegression.interval_iff_score A I₂ α d z
