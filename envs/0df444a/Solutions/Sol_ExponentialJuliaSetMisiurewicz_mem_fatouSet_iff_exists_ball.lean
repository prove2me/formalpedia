-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.mem_fatouSet_iff_exists_ball
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:11:09.465186+00:00
-- url     : https://prove2.me/submissions/8fff4a13-9c61-42fa-9f04-65ad4726704b

import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Definitions.Def_ExpChaotic_Spherical
import Definitions.Def_ExpChaotic_Normality
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_IsNormalSequenceOn_mono

set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution {f : ℂ → ℂ} {z : ℂ} :
    z ∈ fatouSet f ↔ ∃ r : ℝ, 0 < r ∧
      IsNormalSequenceOn (fun n w => ((f^[n]) w : RiemannSphere)) (ball z r) := by
  constructor
  · rintro ⟨U, hU, hz, hnormal⟩
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU z hz
    exact ⟨r, hr, hnormal.mono hball⟩
  · rintro ⟨r, hr, hnormal⟩
    exact ⟨ball z r, isOpen_ball, mem_ball_self hr, hnormal⟩
end ExponentialJuliaSetMisiurewicz
