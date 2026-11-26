-- Prove2me | solution 1 for FourierJacobi.Analysis.i2SpatialPredicate_row1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:46:16.849465+00:00
-- url     : https://prove2.me/submissions/f515f00f-93cd-4529-900d-dbccdbd0328e

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Predicates

set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis
namespace FourierJacobi.Analysis
theorem _root_.solution (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 1 p ↔ (p.1 = 1 ∧ -2 ≤ p.2.1 ∧ -1 ≤ p.2.2) := Iff.rfl
end FourierJacobi.Analysis
