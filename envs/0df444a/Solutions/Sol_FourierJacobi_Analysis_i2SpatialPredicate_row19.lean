-- Prove2me | solution 1 for FourierJacobi.Analysis.i2SpatialPredicate_row19
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:48:23.96352+00:00
-- url     : https://prove2.me/submissions/dc3b6336-fbe3-46c8-903f-e0f45a1574be

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Predicates

set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis
namespace FourierJacobi.Analysis
theorem _root_.solution (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 19 p ↔ (p.1 ≤ 0 ∧ p.2.1 < -1 ∧ p.2.1 ≤ p.2.2 ∧ p.2.1-1 ≤ 2*p.2.2) := Iff.rfl
end FourierJacobi.Analysis
