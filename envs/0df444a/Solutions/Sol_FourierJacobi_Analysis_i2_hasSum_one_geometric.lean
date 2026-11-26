-- Prove2me | solution 1 for FourierJacobi.Analysis.i2_hasSum_one_geometric
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:57:48.949108+00:00
-- url     : https://prove2.me/submissions/b8f87252-1dc4-41da-bcc9-8fddbcf3eddb

import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_FourierJacobi_Analysis_I2Convergence

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
namespace FourierJacobi.Analysis
theorem _root_.solution (C a : ℂ) (ha : ‖a‖ < 1) :
    HasSum (fun n : ℕ => C * a ^ n) (C * (1 - a)⁻¹) :=
  (hasSum_geometric_of_norm_lt_one ha).mul_left C
end FourierJacobi.Analysis
