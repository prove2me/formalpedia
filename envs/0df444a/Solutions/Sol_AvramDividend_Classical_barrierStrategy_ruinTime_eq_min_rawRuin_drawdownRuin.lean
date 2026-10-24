-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_ruinTime_eq_min_rawRuin_drawdownRuin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T11:10:46.611986+00:00
-- url     : https://prove2.me/submissions/4d2a2b77-fd4d-4a1b-9e30-654be938020a

import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_riskProcess_barrier_ruin_piecewise

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-! Pointwise ruin-event disjunction lifts to the minimum of strict ruin times. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hxa : x ≤ a) (ω : Ω) :
    ruinTime X x (barrierStrategy X x a) ω =
      min (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞))
        (⨅ (t : ℝ≥0) (_ : a < runningSup X t ω - X.X t ω), (t : ℝ≥0∞)) := by
  have hevent : ∀ t : ℝ≥0,
      riskProcess X x (barrierStrategy X x a) t ω < 0 ↔
        X.X t ω < -x ∨ a < runningSup X t ω - X.X t ω := by
    intro t
    by_cases ht : t = 0
    · subst t
      have hD0 : barrierStrategy X x a 0 ω = 0 := by
        have hax : x - a ≤ 0 := sub_nonpos.mpr hxa
        simp [barrierStrategy, maxZero, hax]
      have hS0 : runningSup X 0 ω = 0 := by
        unfold runningSup
        have hu : ∀ u : Icc (0 : ℝ≥0) 0, X.X u ω = 0 := fun u => by
          have hs : (u : ℝ≥0) = 0 := le_antisymm u.2.2 u.2.1
          rw [hs, X.X_zero]
        simp [hu, maxZero]
      have hbase : (x < 0) ↔ ((0 : ℝ) < -x ∨ a < 0) := by
        constructor
        · intro h; left; linarith
        · rintro (h | h)
          · linarith
          · linarith
      simpa [riskProcess, hD0, hS0, X.X_zero ω] using hbase
    · have htpos : (0 : ℝ≥0) < t := pos_iff_ne_zero.mpr ht
      rw [riskProcess_barrier_ruin_piecewise X x a hxa t htpos ω]
      constructor
      · rintro (⟨hs, hx⟩ | ⟨hs, hd⟩)
        · exact Or.inl hx
        · exact Or.inr hd
      · rintro (hx | hd)
        · by_cases hs : runningSup X t ω < a - x
          · exact Or.inl ⟨hs, hx⟩
          · exact Or.inr ⟨le_of_not_gt hs, by linarith⟩
        · by_cases hs : runningSup X t ω < a - x
          · exact Or.inl ⟨hs, by linarith⟩
          · exact Or.inr ⟨le_of_not_gt hs, hd⟩
  unfold ruinTime
  simp_rw [hevent]
  simp only [iInf_or, iInf_inf_eq]
