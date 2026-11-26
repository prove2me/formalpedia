-- Prove2me | solution 1 for FourierJacobi.Analysis.i2SpatialPredicate_row3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:46:26.180769+00:00
-- url     : https://prove2.me/submissions/891516ba-a9b0-459b-9d30-cda4dded451f

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Predicates

set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis
namespace FourierJacobi.Analysis
theorem _root_.solution (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 3 p ↔ (1 ≤ p.1 ∧ p.2.1 < -2*p.1 ∧ p.1+p.2.1 ≤ p.2.2 ∧ p.2.1-1 ≤ 2*p.2.2) := Iff.rfl
end FourierJacobi.Analysis
