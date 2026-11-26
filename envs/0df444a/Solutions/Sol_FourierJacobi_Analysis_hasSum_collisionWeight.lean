-- Prove2me | solution 1 for FourierJacobi.Analysis.hasSum_collisionWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:22:57.439529+00:00
-- url     : https://prove2.me/submissions/76234f0e-88a6-4c96-8722-c6d57bbc823c

import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Definitions.Def_FourierJacobi_Algebra_WeylSum
import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Theorems.Thm_FourierJacobi_Analysis_hasSum_collisionProbability

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
namespace FourierJacobi.Analysis
theorem _root_.solution (q : ℂ) (r j h : ℤ)
    (hq₀ : q ≠ 0) (hq₁ : q - 1 ≠ 0) (hq : ‖q⁻¹‖ < 1) :
    HasSum (collisionWeight q r j h) 1 := by
  unfold collisionWeight
  split_ifs
  · exact hasSum_ite_eq 0 1
  · exact hasSum_collisionProbability q hq₀ hq₁ hq
end FourierJacobi.Analysis
