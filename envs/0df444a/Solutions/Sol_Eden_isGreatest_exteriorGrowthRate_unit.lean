-- Prove2me | solution 1 for Eden.isGreatest_exteriorGrowthRate_unit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:13:00.683182+00:00
-- url     : https://prove2.me/submissions/be37f1fc-9fca-4b74-b166-32587ed30a49

import Definitions.Def_Eden_ExteriorLimits
import Definitions.Def_Eden_SelectedSums
import Definitions.Def_Eden_KaplanYorke
import Mathlib.Topology.Order.LiminfLimsup
import Definitions.Def_Eden_ExteriorMaximalGrowth
import Theorems.Thm_Eden_exteriorGrowthRate_eq
import Theorems.Thm_Eden_norm_initialExteriorBasisVector
import Theorems.Thm_Eden_exteriorGrowthRate_basis
import Theorems.Thm_Eden_isGreatest_exteriorRate
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_diagonalLinear_apply
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_planarX_origin
import Theorems.Thm_Eden_planarX_zero_time
import Theorems.Thm_Eden_planarY_origin
import Theorems.Thm_Eden_planarY_zero_time
import Theorems.Thm_Eden_radialAmplitude_zero_time
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_radialDiscriminant_at_zero
import Theorems.Thm_Eden_radialDiscriminant_zero_time
import Theorems.Thm_Eden_squaredRadiusEvolution_at_one
import Theorems.Thm_Eden_squaredRadiusEvolution_at_two
import Theorems.Thm_Eden_squaredRadiusEvolution_at_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
attribute [local simp] Eden.amplitudeSq_at_zero
attribute [local simp] Eden.amplitudeSq_zero_time
attribute [local simp] Eden.blockRotation_apply
attribute [local simp] Eden.diagonalLinear_apply
attribute [local simp] Eden.evolution_zero_time
attribute [local simp] Eden.planarAmplitude_zero_time
attribute [local simp] Eden.planarX_origin
attribute [local simp] Eden.planarX_zero_time
attribute [local simp] Eden.planarY_origin
attribute [local simp] Eden.planarY_zero_time
attribute [local simp] Eden.radialAmplitude_zero_time
attribute [local simp] Eden.radialDiscriminant_at_two
attribute [local simp] Eden.radialDiscriminant_at_zero
attribute [local simp] Eden.radialDiscriminant_zero_time
attribute [local simp] Eden.squaredRadiusEvolution_at_one
attribute [local simp] Eden.squaredRadiusEvolution_at_two
attribute [local simp] Eden.squaredRadiusEvolution_at_zero
attribute [local simp] Eden.squaredRadiusEvolution_zero_time



set_option autoImplicit true
noncomputable section
open Filter Set
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution {k : ℕ} (hk : k ≤ 5) (c : ℝ) (p : PhaseSpace) :
    IsGreatest (exteriorGrowthRate k c p '' {v : ExteriorSpace k | ‖v‖ = 1})
      (spectrumPartialSum (lyapunovExponent c p) k) := by
  obtain ⟨⟨s, hs⟩, hupper⟩ := isGreatest_exteriorRate hk c p
  constructor
  · exact ⟨initialExteriorBasisVector k p s, norm_initialExteriorBasisVector k p s,
      (exteriorGrowthRate_basis k c p s).trans hs⟩
  · rintro r ⟨v, hv, rfl⟩
    have hv₀ : v ≠ 0 := by intro h; simp [h] at hv
    rw [exteriorGrowthRate_eq c p hv₀]
    exact Finset.sup'_le _ _ (fun s _ => hupper ⟨s, rfl⟩)
end Eden
