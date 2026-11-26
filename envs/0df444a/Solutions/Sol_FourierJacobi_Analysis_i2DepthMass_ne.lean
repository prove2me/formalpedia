-- Prove2me | solution 1 for FourierJacobi.Analysis.i2DepthMass_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:36:31.928815+00:00
-- url     : https://prove2.me/submissions/76992dda-9ed5-4d40-8ecc-c64a1ece029e

import Definitions.Def_FourierJacobi_Analysis_I2Complete
import Definitions.Def_FourierJacobi_Analysis_I2Predicates
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_I2Assembly
import Theorems.Thm_FourierJacobi_Analysis_i2_geometric_denominator_ne


set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace FourierJacobi.Analysis
theorem _root_.solution (q : ℂ) (ν : Fin 25)
    (hq₀ : q ≠ 0) (hq₁ : q - 1 ≠ 0) (hq₂ : q - 2 ≠ 0) (hq : ‖q⁻¹‖ < 1) :
    i2DepthMass q ν ≠ 0 := by
  unfold i2DepthMass
  split_ifs
  · exact div_ne_zero hq₂ hq₁
  · exact inv_ne_zero hq₀
  · exact div_ne_zero (pow_ne_zero 2 (inv_ne_zero hq₀)) (i2_geometric_denominator_ne _ hq)
  · exact one_ne_zero
end FourierJacobi.Analysis
