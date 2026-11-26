-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.IsNormalSequenceOn.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:08:26.207024+00:00
-- url     : https://prove2.me/submissions/564c39ed-31f6-4db0-8088-377ae14db8d1

import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Definitions.Def_ExpChaotic_Spherical
import Definitions.Def_ExpChaotic_Normality

set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
namespace IsNormalSequenceOn
theorem _root_.solution {α β : Type*} [TopologicalSpace α] [UniformSpace β]
    {F : ℕ → α → β} {U V : Set α} (h : IsNormalSequenceOn F U) (hVU : V ⊆ U) :
    IsNormalSequenceOn F V := by
  intro φ hφ
  let i : V → U := fun z => ⟨z, hVU z.property⟩
  have hi : Continuous i := continuous_subtype_val.subtype_mk _
  obtain ⟨ψ, hψ, g, hg⟩ := h φ hφ
  exact ⟨ψ, hψ, g ∘ i, hg.comp i hi⟩
end IsNormalSequenceOn
end ExponentialJuliaSetMisiurewicz
