-- Prove2me | solution 1 for AvramDividend.Classical.dividendStrategy_plus_linear_drain_initial_rightLimit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:22:31.716913+00:00
-- url     : https://prove2.me/submissions/9cb9372f-5dcd-4e32-9fba-646b69976c10

import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Topology.UniformSpace.Real
import Mathlib.Tactic
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendPath_real_rightLim_eq_rightLimit
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_plus_linear_drain

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- A continuous deterministic drain contributes no right-hand dividend
    atom at time zero, including when the base policy has an initial jump. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) :
    rightLimit (fun t ω => D t ω + (t : ℝ)) 0 ω = rightLimit D 0 ω := by
  let E : ℝ≥0 → Ω → ℝ := fun t ω => D t ω + (t : ℝ)
  have hED : IsDividendStrategy 𝓕 E :=
    dividendStrategy_plus_linear_drain D hD
  have hmD : Monotone (fun t : ℝ≥0 => D t ω) := hD.2.1 ω
  have hmE : Monotone (fun t : ℝ≥0 => E t ω) := hED.2.1 ω
  have hmR : Monotone (fun t : ℝ => t.toNNReal) := by
    intro a b hab
    exact Real.toNNReal_le_toNNReal hab
  have hlimD : Tendsto (fun s : ℝ => D s.toNNReal ω)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (rightLimit D 0 ω)) := by
    rw [← dividendPath_real_rightLim_eq_rightLimit D ω hmD 0]
    exact ((hmD.comp hmR).tendsto_rightLim (0 : ℝ))
  have hlimE : Tendsto (fun s : ℝ => E s.toNNReal ω)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (rightLimit E 0 ω)) := by
    rw [← dividendPath_real_rightLim_eq_rightLimit E ω hmE 0]
    exact ((hmE.comp hmR).tendsto_rightLim (0 : ℝ))
  have hc : Continuous (fun s : ℝ => (s.toNNReal : ℝ)) := by
    have hf : (fun s : ℝ => (s.toNNReal : ℝ)) =
        (fun s : ℝ => max s 0) := by
      funext s
      rcases le_total 0 s with hs | hs
      · rw [Real.coe_toNNReal s hs, max_eq_left hs]
      · simp [Real.toNNReal_of_nonpos hs, max_eq_right hs]
    rw [hf]
    exact continuous_id.max continuous_const
  have hlimT : Tendsto (fun s : ℝ => (s.toNNReal : ℝ))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (0 : ℝ)) := by
    simpa using (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hlimSum : Tendsto (fun s : ℝ => E s.toNNReal ω)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (rightLimit D 0 ω)) := by
    simpa [E] using hlimD.add hlimT
  exact tendsto_nhds_unique hlimE hlimSum
