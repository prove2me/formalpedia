-- Prove2me | solution 1 for FourierJacobi.Analysis.i2SpatialPredicate_row6
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:46:43.46154+00:00
-- url     : https://prove2.me/submissions/d02d5ee3-a1ad-4112-89c1-0657d16ff213

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Predicates

set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis
namespace FourierJacobi.Analysis
theorem _root_.solution (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 6 p ↔ (1 ≤ p.1 ∧ p.2.1 < -2*p.1 ∧ p.1+p.2.1 ≤ p.2.2 ∧ 2*p.2.2 = p.2.1-2) := Iff.rfl
end FourierJacobi.Analysis
