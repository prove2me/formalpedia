-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_34dbea70_enat_to_ennreal_liminf_commutes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:33:01.733692+00:00
-- url     : https://prove2.me/submissions/9c92769d-9773-4a51-80ed-b38fd85632e2

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter
open scoped ENat ENNReal

/-- Converting an ENat sequence to ENNReal commutes with its liminf. -/
theorem solution (u : ℕ → ℕ∞) :
    ENat.toENNReal (Filter.liminf u atTop) =
      Filter.liminf (fun n : ℕ => ENat.toENNReal (u n)) atTop := by
  simp only [Filter.liminf_eq_iSup_iInf]
  simp_rw [ENat.toENNReal_iSup, ENat.toENNReal_iInf]
