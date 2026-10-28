-- Prove2me | solution 1 for AvramDividend.Classical.chat08_stopped_levy_increment_tendsto_of_right_approximation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T07:28:25.46665+00:00
-- url     : https://prove2.me/submissions/568d486e-c7eb-4b90-9587-be84ff1be693

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open Filter MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal Topology
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ)
    (T : ℕ → Ω → ℝ≥0) (τ : Ω → ℝ≥0) (u : ℝ≥0)
    (hT : ∀ ω, Tendsto (fun n => T n ω) atTop (𝓝 (τ ω)))
    (habove : ∀ ω n, τ ω ≤ T n ω) :
    ∀ ω, Tendsto
      (fun n => X.X (T n ω + u) ω - X.X (T n ω) ω)
      atTop (𝓝 (X.X (τ ω + u) ω - X.X (τ ω) ω)) := by
  intro ω
  have h1 : Tendsto (fun n => T n ω + u) atTop (𝓝[Set.Ici (τ ω + u)] (τ ω + u)) :=
    tendsto_nhdsWithin_iff.2 ⟨(hT ω).add_const u,
      Eventually.of_forall fun n => add_le_add_left (habove ω n) u⟩
  have h2 : Tendsto (fun n => T n ω) atTop (𝓝[Set.Ici (τ ω)] (τ ω)) :=
    tendsto_nhdsWithin_iff.2 ⟨hT ω, Eventually.of_forall fun n => habove ω n⟩
  exact ((X.rightCont ω _).tendsto.comp h1).sub ((X.rightCont ω _).tendsto.comp h2)
