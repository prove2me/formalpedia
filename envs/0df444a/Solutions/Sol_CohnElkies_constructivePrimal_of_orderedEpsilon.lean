-- Prove2me | solution 1 for CohnElkies.constructivePrimal_of_orderedEpsilon
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.753002+00:00
-- url     : https://prove2.me/submissions/7cb280b7-438b-4a54-a391-6069d61ba361

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    (construction : OrderedEpsilonUpperConstruction) :
    ConstructivePrimalUpperBound := by
  intro c hc
  have hclose :
      ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
        construction.limitingRadius ε < c :=
    (tendsto_order.1 construction.limitingRadius_tendsto).2 c hc
  have hpositive :
      ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < ε :=
    self_mem_nhdsWithin
  have hsmall :
      ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
        ε < construction.epsilonBound := by
    exact (tendsto_id.mono_left nhdsWithin_le_nhds).eventually
      (gt_mem_nhds construction.epsilonBound_pos)
  obtain ⟨ε, hεclose, hεpositive, hεsmall⟩ :=
    (hclose.and (hpositive.and hsmall)).exists
  have hradius :
      ∀ᶠ d : ℕ in atTop,
        construction.normalizedRadius ε d < c :=
    (tendsto_order.1
      (construction.normalizedRadius_tendsto ε hεpositive hεsmall)).2
        c hεclose
  filter_upwards [construction.admissibleWitness ε hεpositive hεsmall,
    hradius] with d ⟨f, hf⟩ hr
  exact ⟨f, hf.trans hr.le⟩
end CohnElkies
