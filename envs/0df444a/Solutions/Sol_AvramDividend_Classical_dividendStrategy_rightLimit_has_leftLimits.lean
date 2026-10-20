-- Prove2me | solution 1 for AvramDividend.Classical.dividendStrategy_rightLimit_has_leftLimits
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T22:57:59.239861+00:00
-- url     : https://prove2.me/submissions/68fbae23-67ac-4419-887e-b2752c85ef30

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
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t) :
    ∃ l : ℝ, Tendsto (fun s : ℝ≥0 => rightLimit D s ω) (𝓝[<] t) (𝓝 l) := by
  let f : ℝ≥0 → ℝ := fun s => D s ω
  have hf : Monotone f := hD.2.1 ω
  have heq (u : ℝ≥0) :
      Function.rightLim f u = rightLimit D u ω := by
    have hinf : Function.rightLim f u =
        sInf (f '' Ioi u) := hf.rightLim_eq_sInf
    unfold rightLimit
    calc
      Function.rightLim f u = sInf (f '' Ioi u) := hinf
      _ = ⨅ s : Ioi u, D s.1 ω := by
        simp only [iInf, Set.image_eq_range]
        rfl
  have hmono : Monotone (fun s : ℝ≥0 => rightLimit D s ω) := by
    intro a b hab
    calc
      rightLimit D a ω = Function.rightLim f a := (heq a).symm
      _ ≤ Function.rightLim f b := hf.rightLim hab
      _ = rightLimit D b ω := heq b
  exact ⟨_, hmono.tendsto_leftLim t⟩
