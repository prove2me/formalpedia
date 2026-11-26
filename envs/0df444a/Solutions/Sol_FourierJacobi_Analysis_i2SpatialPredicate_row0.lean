-- Prove2me | solution 1 for FourierJacobi.Analysis.i2SpatialPredicate_row0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:46:11.248961+00:00
-- url     : https://prove2.me/submissions/3acd6790-7978-4a2a-b6ea-853d75a16844

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Predicates

set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis
namespace FourierJacobi.Analysis
theorem _root_.solution (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 0 p ↔ (2 ≤ p.1 ∧ -2*p.1 ≤ p.2.1 ∧ -p.1 ≤ p.2.2) := Iff.rfl
end FourierJacobi.Analysis
