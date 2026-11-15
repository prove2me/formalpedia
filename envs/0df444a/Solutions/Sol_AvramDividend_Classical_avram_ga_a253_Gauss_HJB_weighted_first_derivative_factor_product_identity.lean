-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a253_Gauss_HJB_weighted_first_derivative_factor_product_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:56:27.993363+00:00
-- url     : https://prove2.me/submissions/b3fee78d-92bd-453f-856c-16fc4f0a6160

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem solution
    (f fp alpha beta y : ℝ) :
    Real.exp (-alpha*y)*(fp-alpha*f) =
      Real.exp ((beta-alpha)*y)*
        (Real.exp (-beta*y)*(fp-alpha*f)) := by
  have hExp : Real.exp (-alpha*y) =
      Real.exp ((beta-alpha)*y) * Real.exp (-beta*y) := by
    rw [←Real.exp_add]
    congr 1
    ring
  rw [hExp]
  ring
