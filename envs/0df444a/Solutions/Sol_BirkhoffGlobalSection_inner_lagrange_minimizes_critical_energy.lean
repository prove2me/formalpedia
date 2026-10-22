-- Prove2me | solution 1 for BirkhoffGlobalSection.inner_lagrange_minimizes_critical_energy
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T18:59:52.106384+00:00
-- url     : https://prove2.me/submissions/29bae888-1398-4698-87ea-b5b1e105019d

import Theorems.Thm_BirkhoffGlobalSection_inner_lagrange_le_collinear_critical_energy
import Theorems.Thm_BirkhoffGlobalSection_noncollinear_critical_energy_value
import Theorems.Thm_BirkhoffGlobalSection_inner_lagrange_le_triangular_energy

open BirkhoffGlobalSection

theorem solution (μ : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (L : Phase)
    (hL : IsInnerLagrangePoint μ L) :
    ∀ e ∈ criticalValueSet μ, jacobiHamiltonian μ L ≤ e := by
  intro e he
  obtain ⟨s, hfree, hcrit, hvalue⟩ := he
  rw [← hvalue]
  by_cases haxis : s 1 = 0
  · exact inner_lagrange_le_collinear_critical_energy μ hμ0 hμ1 L hL s hfree hcrit haxis
  · rw [noncollinear_critical_energy_value μ hμ0 hμ1 s hfree hcrit haxis]
    exact inner_lagrange_le_triangular_energy μ hμ0 hμ1 L hL
