-- Prove2me | solution 1 for CohnElkies.radialL1Mass_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:20.470983+00:00
-- url     : https://prove2.me/submissions/3e341583-ae9b-45c4-b629-5e81de7cd986

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Function MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology ENNReal
namespace CohnElkies
theorem _root_.solution {d : ℕ} (g : TestFunction d)
    (hg : g ≠ 0) : 0 < radialL1Mass g := by
  obtain ⟨x, hx⟩ : ∃ x : Euclidean d, g x ≠ 0 := by
    by_contra h
    push Not at h
    apply hg
    ext x
    simpa using! h x
  unfold radialL1Mass
  exact integral_pos_of_integrable_nonneg_nonzero
    g.continuous.norm g.integrable.norm (fun _ => norm_nonneg _)
    (norm_ne_zero_iff.mpr hx)
end CohnElkies
