-- Prove2me | solution 1 for FourierJacobi.Analysis.i2_geometric_denominator_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:28:35.308206+00:00
-- url     : https://prove2.me/submissions/814ebc04-ca49-40b4-8779-95b3265dd830

import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_FourierJacobi_Analysis_I2Convergence

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
namespace FourierJacobi.Analysis
theorem _root_.solution (z : ℂ) (hz : ‖z‖ < 1) : 1 - z ≠ 0 := by
  intro h
  have hz1 : z = 1 := (sub_eq_zero.mp h).symm
  rw [hz1, norm_one] at hz
  exact (lt_irrefl (1 : ℝ)) hz
end FourierJacobi.Analysis
