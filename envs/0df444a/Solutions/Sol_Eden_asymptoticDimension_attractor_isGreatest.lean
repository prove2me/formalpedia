-- Prove2me | solution 1 for Eden.asymptoticDimension_attractor_isGreatest
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:21:08.420935+00:00
-- url     : https://prove2.me/submissions/d9927cf1-84d6-4827-917e-5b52f08b7187

import Definitions.Def_Eden_SpectrumTable
import Definitions.Def_Eden_FiniteTimeDimension
import Definitions.Def_Eden_DimensionTable
import Theorems.Thm_Eden_asymptoticDimension_le_target
import Theorems.Thm_Eden_asymptoticDimension_on_torus
import Theorems.Thm_Eden_torus_nonempty
import Theorems.Thm_Eden_torus_subset_attractor


set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c) :
    IsGreatest (asymptoticDimension c '' attractor) (targetDimension c) := by
  constructor
  · obtain ⟨p, hp⟩ := torus_nonempty
    exact ⟨p, torus_subset_attractor hp, asymptoticDimension_on_torus hc hp⟩
  · rintro d ⟨p, hp, rfl⟩
    exact asymptoticDimension_le_target hc p
end Eden
