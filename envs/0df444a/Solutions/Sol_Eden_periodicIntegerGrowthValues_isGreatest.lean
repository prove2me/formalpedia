-- Prove2me | solution 1 for Eden.periodicIntegerGrowthValues_isGreatest
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:19:05.503621+00:00
-- url     : https://prove2.me/submissions/14ef41ad-58c9-41c4-a85d-0ace5e159ed9

import Definitions.Def_Eden_PeriodicGap
import Definitions.Def_Eden_ExteriorCocycle
import Definitions.Def_Eden_PeriodicGlobalGrowth
import Theorems.Thm_Eden_normalizedLogSingularValues_periodic_le_unit
import Theorems.Thm_Eden_spectrumInterpolation_mono_spectrum
import Theorems.Thm_Eden_spectrumInterpolation_integer
import Theorems.Thm_Eden_singularValueFunction_evolution_eq_exp_interpolation
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_diagonalLinear_apply
import Theorems.Thm_Eden_evolution_origin
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_firstCircle_nonempty
import Theorems.Thm_Eden_mem_positiveReturnSet_iff
import Theorems.Thm_Eden_normalizedLogSingularValues_unit_circle
import Theorems.Thm_Eden_periodicEquilibriumSet_eq_positiveReturnSet
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_planarX_origin
import Theorems.Thm_Eden_planarX_zero_time
import Theorems.Thm_Eden_planarY_origin
import Theorems.Thm_Eden_planarY_zero_time
import Theorems.Thm_Eden_radialAmplitude_zero_time
import Theorems.Thm_Eden_radialDefect_at_one
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_radialDiscriminant_at_zero
import Theorems.Thm_Eden_radialDiscriminant_zero_time
import Theorems.Thm_Eden_singularValueFunction_integer_evolution_zero
import Theorems.Thm_Eden_singularValueFunction_zero
import Theorems.Thm_Eden_spectralProduct_zero
import Theorems.Thm_Eden_spectrumInterpolation_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_at_one
import Theorems.Thm_Eden_squaredRadiusEvolution_at_two
import Theorems.Thm_Eden_squaredRadiusEvolution_at_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
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
attribute [local simp] Eden.radialDefect_at_one
attribute [local simp] Eden.radialDiscriminant_at_two
attribute [local simp] Eden.radialDiscriminant_at_zero
attribute [local simp] Eden.radialDiscriminant_zero_time
attribute [local simp] Eden.singularValueFunction_zero
attribute [local simp] Eden.spectralProduct_zero
attribute [local simp] Eden.spectrumInterpolation_zero
attribute [local simp] Eden.squaredRadiusEvolution_at_one
attribute [local simp] Eden.squaredRadiusEvolution_at_two
attribute [local simp] Eden.squaredRadiusEvolution_at_zero
attribute [local simp] Eden.squaredRadiusEvolution_zero_time



set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden
namespace Eden
theorem _root_.solution {c t : ℝ} (hc : 4 < c)
    (ht : 0 ≤ t) {k : ℕ} (hk : k ≤ 5) :
    IsGreatest (periodicIntegerGrowthValues c k t)
      (Real.exp (t * spectrumPartialSum ![2, 0, -2, -2, -c] k)) := by
  obtain ⟨q, hq⟩ := firstCircle_nonempty (show (0 : ℝ) ≤ 1 by norm_num)
  have hqP : q ∈ periodicEquilibriumSet c := by
    rw [periodicEquilibriumSet_eq_positiveReturnSet (show 0 < c by linarith)]
    exact (mem_positiveReturnSet_iff (by linarith) q).mpr (Or.inr (Or.inl hq))
  rcases eq_or_lt_of_le ht with rfl | ht
  · constructor
    · refine ⟨q, hqP, ?_⟩
      simp [singularValueFunction_integer_evolution_zero hk]
    · rintro x ⟨p, hp, rfl⟩
      simp [singularValueFunction_integer_evolution_zero hk]
  constructor
  · refine ⟨q, hqP, ?_⟩
    dsimp only
    rw [singularValueFunction_evolution_eq_exp_interpolation c ht,
      normalizedLogSingularValues_unit_circle hc ht (Or.inl hq),
      spectrumInterpolation_integer _ hk]
  · rintro x ⟨p, hp, rfl⟩
    dsimp only
    rw [singularValueFunction_evolution_eq_exp_interpolation c ht]
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ ht.le
    exact (spectrumInterpolation_mono_spectrum
      (normalizedLogSingularValues_periodic_le_unit hc ht hp) k).trans_eq
      (spectrumInterpolation_integer _ hk)
end Eden
