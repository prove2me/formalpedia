-- Prove2me | solution 1 for Eden.spectrumPartialSum_nonneg_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:57:08.315424+00:00
-- url     : https://prove2.me/submissions/bf39f494-2a09-4928-b303-411fa2c4404f

import Definitions.Def_Eden_LogarithmicInterpolation
import Definitions.Def_Eden_InterpolationSign
import Theorems.Thm_Eden_spectrumEntry_antitone
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
attribute [local simp] Eden.singularValueFunction_zero
attribute [local simp] Eden.spectralProduct_zero
attribute [local simp] Eden.spectrumInterpolation_zero
attribute [local simp] Eden.squaredRadiusEvolution_at_one
attribute [local simp] Eden.squaredRadiusEvolution_at_two
attribute [local simp] Eden.squaredRadiusEvolution_at_zero
attribute [local simp] Eden.squaredRadiusEvolution_zero_time



set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {a : Fin 5 → ℝ} (ha : Antitone a)
    {k j : ℕ} (hkj : k ≤ j) (hj : j ≤ 5) (hs : 0 ≤ spectrumPartialSum a j) :
    0 ≤ spectrumPartialSum a k := by
  rcases eq_or_lt_of_le hkj with rfl | hkj
  · exact hs
  have hk : k < 5 := lt_of_lt_of_le hkj hj
  by_contra h
  have hneg : spectrumPartialSum a k < 0 := lt_of_not_ge h
  have hkneg : spectrumEntry a k < 0 := by
    by_contra hn
    have hnonneg : 0 ≤ spectrumPartialSum a k := by
      apply Finset.sum_nonneg
      intro i hi
      exact (le_of_not_gt hn).trans
        (spectrumEntry_antitone ha (Finset.mem_range.mp hi).le hk)
    linarith
  have hsum : spectrumPartialSum a j ≤ spectrumPartialSum a k := by
    have hn : (∑ i ∈ Finset.range k, -spectrumEntry a i) ≤
        ∑ i ∈ Finset.range j, -spectrumEntry a i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hkj.le)
      intro i hi hnot
      have hki : k ≤ i := by simp only [Finset.mem_range] at hnot; omega
      have hi₅ : i < 5 := lt_of_lt_of_le (Finset.mem_range.mp hi) hj
      exact neg_nonneg.mpr ((spectrumEntry_antitone ha hki hi₅).trans hkneg.le)
    simpa only [Finset.sum_neg_distrib, neg_le_neg_iff, spectrumPartialSum] using hn
  linarith
end Eden
