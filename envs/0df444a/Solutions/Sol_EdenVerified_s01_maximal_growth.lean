-- Prove2me | solution 1 for EdenVerified.s01_maximal_growth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:55:36.266266+00:00
-- url     : https://prove2.me/submissions/b86ebe46-2b09-4d4c-8deb-9d608e371dad

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_isGreatest_exteriorGrowthRate_nonzero
import Theorems.Thm_Eden_isGreatest_exteriorGrowthRate_unit


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution (c : ℝ) (p : PhaseSpace) (k : ℕ) (hk : k ≤ 5) :
    IsGreatest (exteriorGrowthRate k c p '' {v : ExteriorSpace k | ‖v‖ = 1})
      (spectrumPartialSum (lyapunovExponent c p) k) ∧
    IsGreatest (exteriorGrowthRate k c p '' {v : ExteriorSpace k | v ≠ 0})
      (spectrumPartialSum (lyapunovExponent c p) k) :=
  ⟨isGreatest_exteriorGrowthRate_unit hk c p, isGreatest_exteriorGrowthRate_nonzero hk c p⟩
end EdenVerified
