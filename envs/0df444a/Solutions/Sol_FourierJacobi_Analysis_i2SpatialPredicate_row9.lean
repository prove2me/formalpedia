-- Prove2me | solution 1 for FourierJacobi.Analysis.i2SpatialPredicate_row9
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:47:26.639696+00:00
-- url     : https://prove2.me/submissions/e36e5070-aa23-4222-9a9e-ad81c46d9bb6

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Predicates

set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis
namespace FourierJacobi.Analysis
theorem _root_.solution (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 9 p ↔ (p.1 = 0 ∧ 0 ≤ p.2.1 ∧ -1 ≤ p.2.2) := Iff.rfl
end FourierJacobi.Analysis
