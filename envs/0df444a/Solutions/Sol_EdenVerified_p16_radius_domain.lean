-- Prove2me | solution 1 for EdenVerified.p16_radius_domain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:38:32.881739+00:00
-- url     : https://prove2.me/submissions/74a6c819-8a3a-4cbc-bc25-753d45effd21

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_evolution_mem_attractor
import Theorems.Thm_P2M_Eden_radiusSq__nonneg_5272e4fb8458
import Theorems.Thm_P2M_Eden_radiusSq__nonneg_7729c3bfdb8d


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution (c : ℝ) {p : PhaseSpace} (hp : p ∈ attractor)
    {t : ℝ} (ht : 0 ≤ t) : ∀ τ ∈ Icc (0 : ℝ) t,
      radiusSq₁ (evolution c τ p) ∈ Icc (0 : ℝ) 2 ∧
      radiusSq₂ (evolution c τ p) ∈ Icc (0 : ℝ) 2 := by
  intro τ hτ
  have hA := evolution_mem_attractor c hτ.1 hp
  exact ⟨⟨radiusSq₁_nonneg _, hA.1⟩, ⟨radiusSq₂_nonneg _, hA.2.1⟩⟩
end EdenVerified
