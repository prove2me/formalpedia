-- Prove2me | solution 1 for BirkhoffGlobalSection.inner_lagrange_circle_hamiltonian_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T07:24:43.893973+00:00
-- url     : https://prove2.me/submissions/41129de6-10e8-4a59-b32c-f482ecaced98

import Theorems.Thm_BirkhoffGlobalSection_leviCivita_zero_offset_square_lower_bound
import Theorems.Thm_BirkhoffGlobalSection_inner_lagrange_circle_effective_potential_bound

open BirkhoffGlobalSection

theorem solution (μ : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (L : Phase)
    (hL : IsInnerLagrangePoint μ L) (s : Phase)
    (hr : ((leviCivitaPosition μ s) 0 + μ) ^ 2 +
      ((leviCivitaPosition μ s) 1) ^ 2 = (L 0 + μ) ^ 2) :
    zNormSq s * jacobiHamiltonian μ L ≤ leviCivitaHamiltonian μ 0 s := by
  exact (inner_lagrange_circle_effective_potential_bound μ hμ0 hμ1 L hL s hr).trans
    (leviCivita_zero_offset_square_lower_bound μ s)
