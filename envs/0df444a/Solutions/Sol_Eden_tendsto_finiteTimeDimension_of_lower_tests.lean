-- Prove2me | solution 1 for Eden.tendsto_finiteTimeDimension_of_lower_tests
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:19:02.500871+00:00
-- url     : https://prove2.me/submissions/0bf35136-35a2-4a5c-a17b-a916570a4488

import Definitions.Def_Eden_FiniteTimeKaplanYorke
import Definitions.Def_Eden_DimensionConvergenceCriteria
import Theorems.Thm_Eden_eventually_finiteTimeDimension_lt
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_diagonalLinear_apply
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_finiteTimeDimension_mem_interval
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
open Set Filter
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) (p : PhaseSpace)
    (hlo : ∀ d ∈ Ioo 0 (asymptoticDimension c p),
      ∀ᶠ t in atTop, d ≤ finiteTimeDimension c t p) :
    Tendsto (fun t => finiteTimeDimension c t p) atTop (𝓝 (asymptoticDimension c p)) := by
  apply tendsto_order.mpr
  constructor
  · intro l hl
    by_cases hl₀ : l < 0
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      exact hl₀.trans_le (finiteTimeDimension_mem_interval c ht.le p).1
    let d := (l + asymptoticDimension c p) / 2
    have hd : d ∈ Ioo 0 (asymptoticDimension c p) := by
      constructor <;> dsimp [d] <;> linarith
    filter_upwards [hlo d hd] with t ht
    exact (show l < d by dsimp [d]; linarith).trans_le ht
  · exact fun _ hu => eventually_finiteTimeDimension_lt c p hu
end Eden
