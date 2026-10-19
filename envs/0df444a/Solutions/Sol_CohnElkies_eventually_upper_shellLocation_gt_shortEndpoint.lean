-- Prove2me | solution 1 for CohnElkies.eventually_upper_shellLocation_gt_shortEndpoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:25.301796+00:00
-- url     : https://prove2.me/submissions/115f2939-6bdd-4e4b-998c-379a092c52a6

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_tendsto_upper_one_add_shortEndpoint_scaled

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      shortEndpoint ε + 1 < shellLocation ε := by
  have hid : Tendsto (fun ε : ℝ => ε)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hpow :
      Tendsto (fun ε : ℝ =>
        ε ^ 2 * (ε * (1 + shortEndpoint ε)))
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa using! (hid.pow 2).mul
      tendsto_upper_one_add_shortEndpoint_scaled
  have hsmall :
      ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
        ε ^ 3 * (shortEndpoint ε + 1) < 1 := by
    have hevent := hpow.eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [hevent] with ε hε
    change ε ^ 2 * (ε * (1 + shortEndpoint ε)) < 1
      at hε
    nlinarith
  filter_upwards [self_mem_nhdsWithin, hsmall]
    with ε hε hbound
  change 0 < ε at hε
  have hcube : 0 < ε ^ 3 := pow_pos hε 3
  have hinv : ε ^ 3 * shellLocation ε = 1 := by
    unfold shellLocation
    field_simp [hε.ne']
  have hmul :
      ε ^ 3 * (shortEndpoint ε + 1) <
        ε ^ 3 * shellLocation ε := by
    rw [hinv]
    exact hbound
  nlinarith [hmul]
end CohnElkies
