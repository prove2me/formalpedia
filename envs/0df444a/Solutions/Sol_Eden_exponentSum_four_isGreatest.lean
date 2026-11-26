-- Prove2me | solution 1 for Eden.exponentSum_four_isGreatest
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:18:57.612911+00:00
-- url     : https://prove2.me/submissions/72565ab1-254d-4f27-b9ef-f237f4469cc8

import Definitions.Def_Eden_DimensionTable
import Definitions.Def_Eden_ExponentSums
import Theorems.Thm_Eden_exponentSum_four_bound_and_eq
import Theorems.Thm_Eden_exponentSum_four_eq_iff
import Theorems.Thm_Eden_torus_nonempty
import Theorems.Thm_Eden_torus_subset_attractor


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c) :
    IsGreatest ((fun p => spectrumPartialSum (lyapunovExponent c p) 4) '' attractor) 4 := by
  constructor
  · obtain ⟨p, hp⟩ := torus_nonempty
    exact ⟨p, torus_subset_attractor hp,
      (exponentSum_four_eq_iff hc (torus_subset_attractor hp)).mpr hp⟩
  · rintro x ⟨p, hp, rfl⟩
    exact (exponentSum_four_bound_and_eq hc p).1
end Eden
