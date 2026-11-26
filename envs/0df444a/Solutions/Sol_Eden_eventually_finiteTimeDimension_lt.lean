-- Prove2me | solution 1 for Eden.eventually_finiteTimeDimension_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:17:50.063289+00:00
-- url     : https://prove2.me/submissions/7444260d-f86a-450a-8e15-910f44e459ab

import Definitions.Def_Eden_FiniteTimeKaplanYorke
import Definitions.Def_Eden_DimensionConvergenceCriteria
import Theorems.Thm_Eden_tendsto_spectrumInterpolation_normalized
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_diagonalLinear_apply
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_finiteTimeDimension_eq_kaplanYorke
import Theorems.Thm_Eden_finiteTimeDimension_mem_interval
import Theorems.Thm_Eden_kaplanYorkeDimension_mem_interval
import Theorems.Thm_Eden_lyapunovExponent_antitone
import Theorems.Thm_Eden_normalizedLogSingularValues_antitone
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
import Theorems.Thm_Eden_spectrumInterpolation_neg_iff
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
open Set Filter
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) (p : PhaseSpace) {u : ℝ}
    (hu : asymptoticDimension c p < u) :
    ∀ᶠ t in atTop, finiteTimeDimension c t p < u := by
  by_cases h₅ : 5 < u
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact (finiteTimeDimension_mem_interval c ht.le p).2.trans_lt h₅
  have hb := kaplanYorkeDimension_mem_interval (lyapunovExponent c p)
  let d := (asymptoticDimension c p + u) / 2
  have hd : d ∈ Icc 0 5 := by
    have hb₀ : 0 ≤ asymptoticDimension c p := hb.1
    constructor <;> dsimp [d] <;> linarith
  have hneg : spectrumInterpolation (lyapunovExponent c p) d < 0 :=
    (spectrumInterpolation_neg_iff (lyapunovExponent_antitone c p) hd).mpr
      (by change asymptoticDimension c p < d; dsimp [d]; linarith)
  have he := (tendsto_spectrumInterpolation_normalized c p d).eventually
    (Iio_mem_nhds hneg)
  filter_upwards [he, eventually_gt_atTop (0 : ℝ)] with t htneg ht
  rw [finiteTimeDimension_eq_kaplanYorke c ht p]
  have hlt := (spectrumInterpolation_neg_iff
    (normalizedLogSingularValues_antitone c ht p) hd).mp htneg
  exact hlt.trans (by dsimp [d]; linarith)
end Eden
