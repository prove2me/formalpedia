-- Prove2me | solution 1 for Eden.real_subadditive_eventually_div_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:50:21.171674+00:00
-- url     : https://prove2.me/submissions/74efc8a5-6890-4a11-b3e5-30126cbdde95

import Definitions.Def_Eden_GlobalGrowth
import Mathlib.Analysis.Subadditive
import Mathlib.Algebra.Order.Floor.Semiring
import Definitions.Def_Eden_RealSubadditive
import Theorems.Thm_Eden_real_subadditive_div_le
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
attribute [local simp] Eden.squaredRadiusEvolution_at_one
attribute [local simp] Eden.squaredRadiusEvolution_at_two
attribute [local simp] Eden.squaredRadiusEvolution_at_zero
attribute [local simp] Eden.squaredRadiusEvolution_zero_time



set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden
namespace Eden
theorem _root_.solution {f : ℝ → ℝ} {C : ℝ}
    (hsub : ∀ s t, 0 ≤ s → 0 ≤ t → f (s + t) ≤ f s + f t)
    (hC : 0 ≤ C) (hbound : ∀ t, 0 ≤ t → |f t| ≤ C * t)
    {T L : ℝ} (hT : 0 < T) (hL : f T / T < L) :
    ∀ᶠ t : ℝ in atTop, f t / t < L := by
  have hlim : Tendsto (fun t : ℝ => f T / T + (C + |f T / T|) * T / t)
      atTop (𝓝 (f T / T)) := by
    simpa only [add_zero] using
      (tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id) :
        Tendsto (fun t : ℝ => f T / T + (C + |f T / T|) * T / t)
          atTop (𝓝 (f T / T + 0)))
  filter_upwards [hlim.eventually (gt_mem_nhds hL), eventually_gt_atTop (0 : ℝ)]
    with t ht hpos
  exact (real_subadditive_div_le hsub hC hbound hT hpos).trans_lt ht
end Eden
