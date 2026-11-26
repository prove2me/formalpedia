-- Prove2me | solution 1 for Eden.globalLogGrowth_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:57:50.503799+00:00
-- url     : https://prove2.me/submissions/f3ceb8ce-e08a-4dc1-84e8-78d0abb0a916

import Definitions.Def_Eden_GlobalGrowthLimits
import Definitions.Def_Eden_FiniteTimeDimension
import Definitions.Def_Eden_OrderedStationarySpectrum
import Definitions.Def_Eden_ExactGlobalGrowth
import Theorems.Thm_Eden_singularValueFunction_torus_integer_ge_one
import Theorems.Thm_Eden_singularValueFunction_le_supremum
import Theorems.Thm_Eden_torus_nonempty
import Theorems.Thm_Eden_torus_subset_attractor


set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden
namespace Eden
theorem _root_.solution {k : ℕ} (hk : k ≤ 4) {c t : ℝ}
    (hc : 4 ≤ c) (ht : 0 ≤ t) : 0 ≤ globalLogGrowth c k t := by
  obtain ⟨p, hp⟩ := torus_nonempty
  apply Real.log_nonneg
  exact (singularValueFunction_torus_integer_ge_one hk (by linarith) ht hp).trans
    (singularValueFunction_le_supremum (by omega) hc ht (torus_subset_attractor hp))
end Eden
