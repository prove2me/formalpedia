-- Prove2me | solution 1 for FourierJacobi.Analysis.i2SpatialPredicate_row10
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:47:27.825376+00:00
-- url     : https://prove2.me/submissions/64a56446-e242-4631-a4d7-68142202ae37

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Predicates

set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis
namespace FourierJacobi.Analysis
theorem _root_.solution (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 10 p ↔ (p.1 = 0 ∧ p.2.1 = -1 ∧ -1 ≤ p.2.2) := Iff.rfl
end FourierJacobi.Analysis
