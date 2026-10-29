-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bt_new_original_clock_descending_laplace_crossmul
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T01:05:12.763669+00:00
-- url     : https://prove2.me/submissions/d8a1afb7-98f2-4ba7-ab49-baf2557e022a

import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_original_clock_wh_gap_normalisation
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_original_clock_supremum_lintegral_rate_gap

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- The original exponential-clock descending Laplace factor has
the exact finite-rate cross-multiplied transform, with no division by zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (p : ℝ) (hp : 0 < p)
    (lam : ℝ) (hlam : 0 < lam) (hroot : X.ψ lam = p)
    (β : ℝ) (hβ : 0 ≤ β) (hβlam : β < lam)
    (hgap : X.ψ β < p) :
    let S : Ω × ℝ → ℝ :=
      fun z => runningSup X (Real.toNNReal z.2) z.1
    let D : Ω × ℝ → ℝ :=
      fun z => S z - X.X (Real.toNNReal z.2) z.1
    ENNReal.ofReal (p - X.ψ β) * ENNReal.ofReal lam *
      (∫⁻ z, ENNReal.ofReal (Real.exp (-β * D z))
        ∂(P.prod (expMeasure p))) =
    ENNReal.ofReal (lam - β) * ENNReal.ofReal p := by
  let S : Ω × ℝ → ℝ :=
    fun z => runningSup X (Real.toNNReal z.2) z.1
  let D : Ω × ℝ → ℝ :=
    fun z => S z - X.X (Real.toNNReal z.2) z.1
  let A : ℝ≥0∞ :=
    ∫⁻ z : Ω × ℝ, ENNReal.ofReal (Real.exp (β * S z))
      ∂(P.prod (expMeasure p))
  let B : ℝ≥0∞ :=
    ∫⁻ z : Ω × ℝ, ENNReal.ofReal (Real.exp (-β * D z))
      ∂(P.prod (expMeasure p))
  have hSup : ENNReal.ofReal (lam - β) * A =
      ENNReal.ofReal lam := by
    simpa [A, S] using
      (avram_ws01e_bt_new_original_clock_supremum_lintegral_rate_gap
        X p hp lam hlam hroot β hβlam)
  have hNorm :
      ENNReal.ofReal (p - X.ψ β) * (A * B) =
      ENNReal.ofReal p := by
    simpa [A, B, S, D] using
      (avram_ws01e_bt_new_original_clock_wh_gap_normalisation
        X p hp β hβ hgap)
  change ENNReal.ofReal (p - X.ψ β) * ENNReal.ofReal lam * B =
    ENNReal.ofReal (lam - β) * ENNReal.ofReal p
  calc
    ENNReal.ofReal (p - X.ψ β) * ENNReal.ofReal lam * B =
        ENNReal.ofReal (p - X.ψ β) *
          ((ENNReal.ofReal (lam - β) * A) * B) := by
            rw [hSup]
            ac_rfl
    _ = ENNReal.ofReal (lam - β) *
          (ENNReal.ofReal (p - X.ψ β) * (A * B)) := by ac_rfl
    _ = ENNReal.ofReal (lam - β) * ENNReal.ofReal p := by rw [hNorm]
