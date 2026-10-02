-- Prove2me | solution 1 for AvramDividend.Classical.ruinTime_shift_add_eq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T22:54:43.414825+00:00
-- url     : https://prove2.me/submissions/0d7e6695-f611-4d5d-ba17-b120eb8f9dc4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology NNReal ENNReal AvramDividend.Classical in
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x c : ℝ)
    (hc : 0 ≤ c)
    (hcx : c < x)
    (E : ℝ≥0 → Ω → ℝ)
    (hE : IsAdmissibleLe X c (ENNReal.ofReal c) E)
    (ω : Ω) :
    ruinTime X x (fun t ω => if t = 0 then 0 else (x - c) + E t ω) ω
      = ruinTime X c E ω := by
  have hE0 : E 0 ω = 0 := hE.1.1.1 ω
  have key : ∀ t : ℝ≥0,
      (riskProcess X x (fun t ω => if t = 0 then 0 else (x - c) + E t ω) t ω < 0) ↔
        (riskProcess X c E t ω < 0) := by
    intro t
    unfold riskProcess
    by_cases ht : t = 0
    · subst ht
      simp only [X.X_zero ω, hE0, if_true]
      constructor <;> intro h <;> linarith
    · simp only [if_neg ht]
      constructor <;> intro h <;> linarith
  unfold ruinTime
  congr 1
  funext t
  rw [propext (key t)]

