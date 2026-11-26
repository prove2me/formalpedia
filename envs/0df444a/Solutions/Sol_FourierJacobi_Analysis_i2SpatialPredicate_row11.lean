-- Prove2me | solution 1 for FourierJacobi.Analysis.i2SpatialPredicate_row11
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:47:28.86175+00:00
-- url     : https://prove2.me/submissions/cd605406-29e9-456c-b713-a127668e7b3e

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Predicates

set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis
namespace FourierJacobi.Analysis
theorem _root_.solution (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 11 p ↔ (p.1 = 0 ∧ -1 ≤ p.2.1 ∧ p.2.2 ≤ -2) := Iff.rfl
end FourierJacobi.Analysis
