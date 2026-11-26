-- Prove2me | solution 1 for Eden.globalLyapunovDimension_attractor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:11:20.784653+00:00
-- url     : https://prove2.me/submissions/2cc6bd72-dc35-4666-aff9-7be990541f8f

import Definitions.Def_Eden_SingularValueFunction
import Definitions.Def_Eden_VolumeGrowth
import Definitions.Def_Eden_FiniteTimeDimension
import Theorems.Thm_Eden_supremum_finiteTimeDimension_attractor

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c) :
    globalLyapunovDimension c attractor = 4 + 4 / c := by
  have heq : {v : ℝ | ∃ t : ℝ, 0 < t ∧ v = sSup (finiteTimeDimension c t '' attractor)} =
      {targetDimension c} := by
    ext v
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact (supremum_finiteTimeDimension_attractor hc ht)
    · intro hv
      have hv' : v = targetDimension c := hv
      refine ⟨1, by norm_num, ?_⟩
      rw [supremum_finiteTimeDimension_attractor hc (by norm_num), hv']
  unfold globalLyapunovDimension
  rw [heq, csInf_singleton]
  rfl
end Eden
