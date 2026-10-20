-- Prove2me | solution 1 for AvramDividend.Classical.dividendStrategy_rightLimit_rightContinuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T22:57:49.284796+00:00
-- url     : https://prove2.me/submissions/4301bdbb-47bf-413a-af09-b72e23a393c3

import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) :
    ContinuousWithinAt (fun s : ℝ≥0 => rightLimit D s ω) (Ici t) t := by
  let f : ℝ≥0 → ℝ := fun s => D s ω
  have hmono : Monotone f := hD.2.1 ω
  have hright (u : ℝ≥0) :
      Function.rightLim f u = rightLimit D u ω := by
    have hinf : Function.rightLim f u =
        sInf (f '' Ioi u) := hmono.rightLim_eq_sInf
    unfold rightLimit
    calc
      Function.rightLim f u = sInf (f '' Ioi u) := hinf
      _ = ⨅ s : Ioi u, D s.1 ω := by
        simp only [iInf, Set.image_eq_range]
        rfl
  have hcont : ContinuousWithinAt (Function.rightLim f) (Ici t) t :=
    continuousWithinAt_rightLim_Ici (hmono.tendsto_rightLim t)
  have heq : (fun s : ℝ≥0 => rightLimit D s ω) =
      Function.rightLim f := by
    funext u
    exact (hright u).symm
  rw [heq]
  exact hcont
