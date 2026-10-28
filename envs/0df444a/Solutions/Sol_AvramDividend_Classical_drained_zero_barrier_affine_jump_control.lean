-- Prove2me | solution 1 for AvramDividend.Classical.drained_zero_barrier_affine_jump_control
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:50:41.333743+00:00
-- url     : https://prove2.me/submissions/2c355390-2b77-4026-bd88-ba209837e9c3

import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_plus_linear_drain
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_plus_linear_drain_initial_rightLimit
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_isDividendStrategy_nonnegative_barrier
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_right_increment_formula
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_plus_linear_drain_ruinTime_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- For any affine verification function on nonnegative reserves, the drained
    zero-barrier admissible control obeys every formal lump-sum jump inequality,
    including its nontrivial initial jump. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (hx : 0 ≤ x)
    (w : ℝ → ℝ) (hw_affine : ∀ y, 0 ≤ y → w y = y - 1) :
    ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) <
        ruinTime X x
          (fun s ω => barrierStrategy X x 0 s ω + (s : ℝ)) ω) →
      rightLimit (fun s ω => barrierStrategy X x 0 s ω + (s : ℝ)) t ω -
          (barrierStrategy X x 0 t ω + (t : ℝ)) ≤
        w (riskProcess X x
          (fun s ω => barrierStrategy X x 0 s ω + (s : ℝ)) t ω) -
        w (riskProcess X x
          (fun s ω => barrierStrategy X x 0 s ω + (s : ℝ)) t ω -
            (rightLimit
              (fun s ω => barrierStrategy X x 0 s ω + (s : ℝ)) t ω -
              (barrierStrategy X x 0 t ω + (t : ℝ)))) := by
  let B : ℝ≥0 → Ω → ℝ := barrierStrategy X x 0
  let D : ℝ≥0 → Ω → ℝ := fun t ω => B t ω + (t : ℝ)
  have hB : IsDividendStrategy 𝓕 B := by
    exact barrierStrategy_isDividendStrategy_nonnegative_barrier X x 0 hx le_rfl
  have hD : IsDividendStrategy 𝓕 D :=
    dividendStrategy_plus_linear_drain B hB
  have hrzero : ∀ ω : Ω, ruinTime X x D ω = 0 := by
    intro ω
    exact barrierStrategy_plus_linear_drain_ruinTime_zero X x hx ω
  change ∀ (ω : Ω) (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
    rightLimit D t ω - D t ω ≤
      w (riskProcess X x D t ω) -
        w (riskProcess X x D t ω - (rightLimit D t ω - D t ω))
  intro ω t ht
  rcases ht with ht | ht
  · subst t
    have hright : rightLimit D 0 ω = rightLimit B 0 ω :=
      dividendStrategy_plus_linear_drain_initial_rightLimit B hB ω
    have hbar : rightLimit B 0 ω - B 0 ω = x := by
      simpa [B, hx] using
        (barrierStrategy_right_increment_formula X x 0 ω 0)
    have hjump : rightLimit D 0 ω - D 0 ω = x := by
      rw [hright, hD.1 ω]
      simpa only [hB.1 ω] using hbar
    have hrisk : riskProcess X x D 0 ω = x := by
      simp [riskProcess, X.X_zero ω, hD.1 ω]
    rw [hjump, hrisk, sub_self, hw_affine x hx, hw_affine 0 le_rfl]
    linarith
  · rw [hrzero ω] at ht
    exact False.elim ((not_lt_of_ge bot_le) ht)
