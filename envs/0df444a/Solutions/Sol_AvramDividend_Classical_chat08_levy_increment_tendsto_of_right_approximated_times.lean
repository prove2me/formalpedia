-- Prove2me | solution 1 for AvramDividend.Classical.chat08_levy_increment_tendsto_of_right_approximated_times
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T23:31:16.84167+00:00
-- url     : https://prove2.me/submissions/3991a172-28f4-4d07-a1e5-5d3a1e0362f0

import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.ContinuousOn
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-! Right-continuous Lévy increments converge along time approximations from above. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (ω : Ω)
    (T : ℕ → ℝ≥0) (t u : ℝ≥0)
    (hT : Tendsto T atTop (𝓝 t)) (hbelow : ∀ n, t ≤ T n) :
    Tendsto (fun n => X.X (T n + u) ω - X.X (T n) ω)
      atTop (𝓝 (X.X (t + u) ω - X.X t ω)) := by
  have hTwithin : Tendsto T atTop (𝓝[Set.Ici t] t) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hT, Filter.Eventually.of_forall (fun n => hbelow n)⟩
  have hTu : Tendsto (fun n => T n + u) atTop (𝓝 (t + u)) :=
    hT.add tendsto_const_nhds
  have hTuw : Tendsto (fun n => T n + u) atTop (𝓝[Set.Ici (t + u)] (t + u)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hTu, Filter.Eventually.of_forall
        (fun n => by simpa only [Set.mem_Ici, add_comm] using
          (add_le_add_right (hbelow n) u))⟩
  have hX0 : Tendsto (fun n => X.X (T n) ω) atTop (𝓝 (X.X t ω)) :=
    (X.rightCont ω t).tendsto.comp hTwithin
  have hXu : Tendsto (fun n => X.X (T n + u) ω) atTop (𝓝 (X.X (t + u) ω)) :=
    (X.rightCont ω (t + u)).tendsto.comp hTuw
  exact hXu.sub hX0
