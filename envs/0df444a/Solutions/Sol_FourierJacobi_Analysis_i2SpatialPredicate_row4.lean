-- Prove2me | solution 1 for FourierJacobi.Analysis.i2SpatialPredicate_row4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:46:27.140585+00:00
-- url     : https://prove2.me/submissions/fbe60251-6dcc-4be3-a717-7d2a808c5d12

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Predicates

set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis
namespace FourierJacobi.Analysis
theorem _root_.solution (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 4 p ↔ (1 ≤ p.1 ∧ p.2.1 < -2*p.1 ∧ p.1+p.2.1 ≤ p.2.2 ∧ 2*p.2.2 = p.2.1-2) := Iff.rfl
end FourierJacobi.Analysis
