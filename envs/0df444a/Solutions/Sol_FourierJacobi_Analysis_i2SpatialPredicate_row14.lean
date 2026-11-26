-- Prove2me | solution 1 for FourierJacobi.Analysis.i2SpatialPredicate_row14
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:47:55.717909+00:00
-- url     : https://prove2.me/submissions/edfe8d61-dedb-4100-b5bd-bfca718726d2

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Predicates

set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis
namespace FourierJacobi.Analysis
theorem _root_.solution (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 14 p ↔ (p.1 = -1 ∧ p.2.1 = -1 ∧ p.2.2 ≤ -2) := Iff.rfl
end FourierJacobi.Analysis
