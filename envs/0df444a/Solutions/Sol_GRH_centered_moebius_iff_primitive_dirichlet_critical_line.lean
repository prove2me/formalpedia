-- Prove2me | solution 1 for GRH.centered_moebius_iff_primitive_dirichlet_critical_line
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T00:47:15.033421+00:00
-- url     : https://prove2.me/submissions/22c9ea58-e6fe-419a-ac8f-b27f50ba70a5

import Theorems.Thm_GRH_centered_moebius_at_modulus_iff_dirichlet_zero_free
import Theorems.Thm_GRH_grh_critical_line_iff

open GRH.OneSidedMoebius GRH.FactorialMoebius

theorem solution : centeredBound ↔
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      ∀ s : ℂ, 0 < s.re → s.re < 1 → χ.LFunction s = 0 → s.re = 1/2 := by
  rw [GRH.grh_critical_line_iff]
  constructor
  · intro h q inst
    have levelEquiv := GRH.centered_moebius_at_modulus_iff_dirichlet_zero_free q
    exact levelEquiv.2.1.mp (levelEquiv.1.mp (h q))
  · intro h q inst
    have levelEquiv := GRH.centered_moebius_at_modulus_iff_dirichlet_zero_free q
    exact levelEquiv.1.mpr (levelEquiv.2.1.mpr (h q))
