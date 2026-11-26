-- Prove2me | solution 1 for FourierJacobi.Analysis.i2SpatialPredicate_row17
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:48:15.079439+00:00
-- url     : https://prove2.me/submissions/77b02442-9846-495d-b381-ecf7835efe65

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Predicates

set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis
namespace FourierJacobi.Analysis
theorem _root_.solution (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 17 p ↔ (p.1 ≤ -2 ∧ p.2.1 = -1 ∧ p.2.2 ≤ -2) := Iff.rfl
end FourierJacobi.Analysis
