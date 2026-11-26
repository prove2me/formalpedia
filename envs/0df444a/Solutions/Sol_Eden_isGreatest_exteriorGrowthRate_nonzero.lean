-- Prove2me | solution 1 for Eden.isGreatest_exteriorGrowthRate_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:13:02.879752+00:00
-- url     : https://prove2.me/submissions/351611ec-210c-4d92-bee8-efc56b35d817

import Definitions.Def_Eden_ExteriorLimits
import Definitions.Def_Eden_SelectedSums
import Definitions.Def_Eden_KaplanYorke
import Mathlib.Topology.Order.LiminfLimsup
import Definitions.Def_Eden_ExteriorMaximalGrowth
import Theorems.Thm_Eden_exteriorGrowthRate_eq
import Theorems.Thm_Eden_initialExteriorBasisVector_ne_zero
import Theorems.Thm_Eden_exteriorGrowthRate_basis
import Theorems.Thm_Eden_isGreatest_exteriorRate

set_option autoImplicit true
noncomputable section
open Filter Set
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution {k : ℕ} (hk : k ≤ 5) (c : ℝ) (p : PhaseSpace) :
    IsGreatest (exteriorGrowthRate k c p '' {v : ExteriorSpace k | v ≠ 0})
      (spectrumPartialSum (lyapunovExponent c p) k) := by
  obtain ⟨⟨s, hs⟩, hupper⟩ := isGreatest_exteriorRate hk c p
  constructor
  · exact ⟨initialExteriorBasisVector k p s, initialExteriorBasisVector_ne_zero k p s,
      (exteriorGrowthRate_basis k c p s).trans hs⟩
  · rintro r ⟨v, hv, rfl⟩
    rw [exteriorGrowthRate_eq c p hv]
    exact Finset.sup'_le _ _ (fun s _ => hupper ⟨s, rfl⟩)
end Eden
