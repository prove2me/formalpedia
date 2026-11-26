-- Prove2me | solution 1 for EdenVerified.p18_zero_defect_entire_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:38:28.365464+00:00
-- url     : https://prove2.me/submissions/578f741b-9363-4a97-873b-a6c4012998e0

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_evolution_mem_torus
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_volumeDefect_eq_zero_iff
attribute [local simp] Eden.evolution_zero_time



set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution (c : ℝ) {t : ℝ} (ht : 0 < t)
    {p : PhaseSpace} (hp : p ∈ attractor) :
    volumeDefect t p = 0 ↔ ∀ τ ∈ Icc (0 : ℝ) t,
      radiusSq₁ (evolution c τ p) = 1 ∧ radiusSq₂ (evolution c τ p) = 1 := by
  constructor
  · intro h τ hτ
    have hT := evolution_mem_torus c hτ.1 ((volumeDefect_eq_zero_iff ht hp).1 h)
    exact ⟨hT.1, hT.2.1⟩
  · intro h
    have h0 := h 0 ⟨le_rfl, ht.le⟩
    rw [evolution_zero_time] at h0
    exact (volumeDefect_eq_zero_iff ht hp).2 ⟨h0.1, h0.2, hp.2.2⟩
end EdenVerified
