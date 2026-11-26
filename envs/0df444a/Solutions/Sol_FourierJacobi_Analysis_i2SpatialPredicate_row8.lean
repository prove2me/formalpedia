-- Prove2me | solution 1 for FourierJacobi.Analysis.i2SpatialPredicate_row8
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:47:25.556622+00:00
-- url     : https://prove2.me/submissions/37643b79-03df-4738-9552-d57435113557

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Predicates

set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis
namespace FourierJacobi.Analysis
theorem _root_.solution (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 8 p ↔ (1 ≤ p.1 ∧ p.2.1 < -2*p.1 ∧ p.2.2 < p.1+p.2.1) := Iff.rfl
end FourierJacobi.Analysis
