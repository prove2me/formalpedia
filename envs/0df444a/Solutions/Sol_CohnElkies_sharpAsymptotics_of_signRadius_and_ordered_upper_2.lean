-- Prove2me | solution 2 for CohnElkies.sharpAsymptotics_of_signRadius_and_ordered_upper
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T13:28:46.641109+00:00
-- url     : https://prove2.me/submissions/8c696b7c-6ff2-47b0-9e87-2963a23c4c7b

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_sharpPackingRoot_of_sharpQuotient
import Theorems.Thm_CohnElkies_sharpLog_of_sharpQuotient
import Theorems.Thm_CohnElkies_sharpBinaryLog_of_sharpQuotient
import Theorems.Thm_CohnElkies_eventualUpperBound_of_constructivePrimal
import Theorems.Thm_CohnElkies_sharpQuotient_of_eventual_bounds
import Theorems.Thm_CohnElkies_eventualLowerBound_of_uniform_and_constructive
import Theorems.Thm_CohnElkies_uniformAdmissibleLowerBound_of_signRadius
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Topology
theorem h47_constructive_of_ordered (construction : CohnElkies.OrderedEpsilonUpperConstruction) :
    CohnElkies.ConstructivePrimalUpperBound := by
  intro c hc
  have h1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), construction.limitingRadius ε < c :=
    construction.limitingRadius_tendsto.eventually (gt_mem_nhds hc)
  have h2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < construction.epsilonBound :=
    nhdsWithin_le_nhds (gt_mem_nhds construction.epsilonBound_pos)
  have h3 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  obtain ⟨ε, hε1, hε2, hε3⟩ := (h1.and (h2.and h3)).exists
  have hlim := construction.normalizedRadius_tendsto ε hε3 hε2
  filter_upwards [hlim.eventually (gt_mem_nhds hε1),
    construction.admissibleWitness ε hε3 hε2] with d hd ⟨f, hf⟩
  exact ⟨f, hf.trans hd.le⟩

theorem h47_sharp_all (hlower : CohnElkies.UniformAdmissibleLowerBound)
    (construction : CohnElkies.OrderedEpsilonUpperConstruction) :
    CohnElkies.SharpQuotientAsymptotic ∧ CohnElkies.SharpPackingRootAsymptotic ∧
      CohnElkies.SharpLogAsymptotic ∧ CohnElkies.SharpBinaryLogAsymptotic := by
  have hc := h47_constructive_of_ordered construction
  have hq := CohnElkies.sharpQuotient_of_eventual_bounds
    (CohnElkies.eventualLowerBound_of_uniform_and_constructive hlower hc)
    (CohnElkies.eventualUpperBound_of_constructivePrimal hc)
  exact ⟨hq, CohnElkies.sharpPackingRoot_of_sharpQuotient hq, CohnElkies.sharpLog_of_sharpQuotient hq,
    CohnElkies.sharpBinaryLog_of_sharpQuotient hq⟩

theorem solution
    (hsign : UniformAntiFourierSignRadius)
    (construction : OrderedEpsilonUpperConstruction) :
    SharpQuotientAsymptotic ∧ SharpPackingRootAsymptotic ∧
      SharpLogAsymptotic ∧ SharpBinaryLogAsymptotic := by
  exact h47_sharp_all (CohnElkies.uniformAdmissibleLowerBound_of_signRadius hsign) construction

