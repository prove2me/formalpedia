-- Prove2me | solution 1 for FourierJacobi.Analysis.i2SpatialPredicate_row21
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:48:29.540097+00:00
-- url     : https://prove2.me/submissions/d1124939-206a-4b7f-b8e7-041c989ec7b2

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Predicates

set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis
namespace FourierJacobi.Analysis
theorem _root_.solution (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 21 p ↔ (p.1 ≤ 0 ∧ p.2.1 < -1 ∧ p.2.1 ≤ p.2.2 ∧ 2*p.2.2 = p.2.1-2) := Iff.rfl
end FourierJacobi.Analysis
