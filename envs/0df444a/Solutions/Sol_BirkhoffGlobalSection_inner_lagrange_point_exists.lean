-- Prove2me | solution 1 for BirkhoffGlobalSection.inner_lagrange_point_exists
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T23:41:39.001329+00:00
-- url     : https://prove2.me/submissions/92d2f410-8e67-40a5-8d53-92e9630d2b2a

import Theorems.Thm_BirkhoffGlobalSection_inner_collinear_force_polynomial_root
import Theorems.Thm_BirkhoffGlobalSection_inner_collinear_polynomial_root_is_equilibrium

open BirkhoffGlobalSection

theorem solution (μ : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1) :
    ∃ L : Phase, IsInnerLagrangePoint μ L := by
  rcases inner_collinear_force_polynomial_root μ hμ0 hμ1 with
    ⟨x, hxlo, hxhi, hpoly⟩
  exact ⟨![x, 0, 0, -x],
    inner_collinear_polynomial_root_is_equilibrium μ hμ0 hμ1 x hxlo hxhi hpoly⟩
