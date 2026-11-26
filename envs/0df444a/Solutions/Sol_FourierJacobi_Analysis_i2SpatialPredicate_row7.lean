-- Prove2me | solution 1 for FourierJacobi.Analysis.i2SpatialPredicate_row7
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:47:23.159547+00:00
-- url     : https://prove2.me/submissions/9f3c51e0-de0a-4130-8f4e-76be2a0f499a

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Predicates

set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis
namespace FourierJacobi.Analysis
theorem _root_.solution (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 7 p ↔ (1 ≤ p.1 ∧ p.2.1 < -2*p.1 ∧ p.1+p.2.1 ≤ p.2.2 ∧ 2*p.2.2 ≤ p.2.1-3) := Iff.rfl
end FourierJacobi.Analysis
