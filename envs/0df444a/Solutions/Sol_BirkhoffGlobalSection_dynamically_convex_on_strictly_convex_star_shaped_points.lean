-- Prove2me | solution 1 for BirkhoffGlobalSection.dynamically_convex_on_strictly_convex_star_shaped_points
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-29T17:09:47.799979+00:00
-- url     : https://prove2.me/submissions/32c7fc43-1810-4a8b-a21f-c3b65e596d11

import Theorems.Thm_BirkhoffGlobalSection_strict_convex_orbit_positive_canonical_model
import Theorems.Thm_BirkhoffGlobalSection_radial_contact_transverse_angle_conjugacy
import Theorems.Thm_BirkhoffGlobalSection_positive_moving_frame_winding
import Mathlib.Tactic.Linarith

open BirkhoffGlobalSection HryniewiczCriterion

theorem solution (G : Phase → ℝ) :
    IsDynamicallyConvexOn G {y | IsStrictlyConvexStarShapedAt G y} := by
  intro x T hx Y hY0 hY v hv hvne θ hθc hθ
  have hm := strict_convex_orbit_positive_canonical_model G x T hx Y hY0 hY
  obtain ⟨S, hSc, hSpos, hd⟩ := hm.positive_generator
  have hw := positive_moving_frame_winding
    (canonicalRadialFrame G x) (canonicalTransversePath G x T Y) T hx.1
    hm.symplectic hm.halfPlane hm.continuous hm.endpoint
    hm.transverse_continuous hm.transverse_det hm.transverse_zero S hSc hSpos hd
  obtain ⟨s, β, a, hs, hβ, ha, ha2π, he⟩ :=
    radial_contact_transverse_angle_conjugacy G x T hx Y hY0 hY v hv hvne θ hθc hθ
  have hdmem : (β 1 - s) / (2 * Real.pi) ∈
      windingInterval (canonicalTransversePath G x T Y) := ⟨s, ⟨hs.1, hs.2.le⟩, β, hβ, rfl⟩
  have hb := hw _ hdmem
  have hπ : 0 < 2 * Real.pi := by linarith [Real.pi_pos]
  have hβend : s + 2 * Real.pi < β 1 := by
    have := (lt_div_iff₀ hπ).mp hb
    linarith
  have haend := ha hβend
  rw [ha2π] at haend
  rw [he]
  linarith
