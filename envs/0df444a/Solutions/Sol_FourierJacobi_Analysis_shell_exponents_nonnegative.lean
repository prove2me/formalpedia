-- Prove2me | solution 1 for FourierJacobi.Analysis.shell_exponents_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:21:46.82216+00:00
-- url     : https://prove2.me/submissions/1608fcbc-4d02-40e9-bf08-486e28f77856

import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Definitions.Def_FourierJacobi_Algebra_WeylSum
import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Theorems.Thm_FourierJacobi_Valuations_cartanIndices_nonnegative


set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
namespace FourierJacobi.Analysis
theorem _root_.solution (r k j h : ℤ) (c : ℕ) :
    0 ≤ (cartanIndices r k j h c).1 / 2 ∧
    0 ≤ (cartanIndices r k j h c).2 := by
  have hc := cartanIndices_nonnegative r k j h c (by omega)
  constructor
  · omega
  · exact hc.2
end FourierJacobi.Analysis
