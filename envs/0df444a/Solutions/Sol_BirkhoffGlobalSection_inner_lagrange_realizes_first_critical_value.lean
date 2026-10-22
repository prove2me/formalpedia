-- Prove2me | solution 1 for BirkhoffGlobalSection.inner_lagrange_realizes_first_critical_value
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T18:53:30.80312+00:00
-- url     : https://prove2.me/submissions/ce547440-ba3d-4889-a902-dd2232a4ea7d

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Theorems.Thm_BirkhoffGlobalSection_inner_lagrange_point_exists
import Theorems.Thm_BirkhoffGlobalSection_inner_lagrange_minimizes_critical_energy

open BirkhoffGlobalSection

theorem solution (μ : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1) :
    ∃ L : Phase, IsInnerLagrangePoint μ L ∧
      jacobiHamiltonian μ L = firstCriticalValue μ := by
  obtain ⟨L, hL⟩ := inner_lagrange_point_exists μ hμ0 hμ1
  have hmem : jacobiHamiltonian μ L ∈ criticalValueSet μ :=
    ⟨L, hL.1, hL.2.1, rfl⟩
  have hleast : IsLeast (criticalValueSet μ) (jacobiHamiltonian μ L) :=
    ⟨hmem, inner_lagrange_minimizes_critical_energy μ hμ0 hμ1 L hL⟩
  exact ⟨L, hL, hleast.csInf_eq.symm⟩
