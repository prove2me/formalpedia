-- Prove2me | solution 1 for FourierJacobi.Analysis.i2SpatialPredicate_row23
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:48:51.620297+00:00
-- url     : https://prove2.me/submissions/da1f648b-e4d6-417c-8268-f3714e554564

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Predicates

set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis
namespace FourierJacobi.Analysis
theorem _root_.solution (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 23 p ↔ (p.1 ≤ 0 ∧ p.2.1 < -1 ∧ p.2.1 ≤ p.2.2 ∧ 2*p.2.2 ≤ p.2.1-3) := Iff.rfl
end FourierJacobi.Analysis
