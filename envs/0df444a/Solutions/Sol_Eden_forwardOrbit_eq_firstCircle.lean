-- Prove2me | solution 1 for Eden.forwardOrbit_eq_firstCircle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:14:55.411065+00:00
-- url     : https://prove2.me/submissions/48f3873e-4ae2-486a-8748-c0c22c7cb012

import Definitions.Def_Eden_PeriodicSets
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Definitions.Def_Eden_CircleOrbits
import Theorems.Thm_Eden_exists_planar_time_on_stationary_radius
import Theorems.Thm_Eden_firstCircle_invariant
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_diagonalLinear_apply
import Theorems.Thm_Eden_evolution_origin
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
import Theorems.Thm_P2M_Eden_radiusSq__eq_zero_iff_31ccc9756278
attribute [local simp] Eden.amplitudeSq_at_zero
attribute [local simp] Eden.amplitudeSq_zero_time
attribute [local simp] Eden.blockRotation_apply
attribute [local simp] Eden.diagonalLinear_apply
attribute [local simp] Eden.evolution_origin
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
open Set
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) {s : ℝ} (hs : s = 1 ∨ s = 2)
    {p : PhaseSpace} (hp : p ∈ firstCircle s) : forwardOrbit c p = firstCircle s := by
  ext q
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact firstCircle_invariant c hs ht hp
  · intro hq
    obtain ⟨t, ht, hx, hy⟩ := exists_planar_time_on_stationary_radius
      (show (0 : ℝ) < 1 by norm_num) hs hp.1 hq.1
    refine ⟨t, ht.le, ?_⟩
    obtain ⟨hp₂, hp₃⟩ := (radiusSq₂_eq_zero_iff p).mp hp.2.1
    obtain ⟨hq₂, hq₃⟩ := (radiusSq₂_eq_zero_iff q).mp hq.2.1
    ext i
    fin_cases i <;> simp [evolution, hx, hy, hp₂, hp₃, hq₂, hq₃, hp.2.2, hq.2.2]
end Eden
