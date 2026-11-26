-- Prove2me | solution 1 for Eden.finiteTimeDimension_eq_kaplanYorke
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:14:27.118709+00:00
-- url     : https://prove2.me/submissions/0a78843f-a583-4aed-b6a4-54d3800becb9

import Definitions.Def_Eden_InterpolationSign
import Definitions.Def_Eden_FiniteTimeKaplanYorke
import Theorems.Thm_Eden_admissibleDimensions_evolution_eq
import Theorems.Thm_Eden_finiteTimeDimension_isGreatest
import Theorems.Thm_Eden_kaplanYorkeDimension_mem_interval


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) {t : ℝ} (ht : 0 < t)
    (p : PhaseSpace) :
    finiteTimeDimension c t p =
      kaplanYorkeDimension (normalizedLogSingularValues c t p) := by
  have hmax := finiteTimeDimension_isGreatest c ht.le p
  rw [admissibleDimensions_evolution_eq c ht p] at hmax
  exact le_antisymm hmax.1.2 (hmax.2
    ⟨(kaplanYorkeDimension_mem_interval (normalizedLogSingularValues c t p)).1, le_rfl⟩)
end Eden
