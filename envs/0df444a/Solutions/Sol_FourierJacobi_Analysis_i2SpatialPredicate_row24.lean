-- Prove2me | solution 1 for FourierJacobi.Analysis.i2SpatialPredicate_row24
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:48:52.873745+00:00
-- url     : https://prove2.me/submissions/e50bf2af-3cf8-4b2b-8b7f-4a930cf463fd

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Predicates

set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis
namespace FourierJacobi.Analysis
theorem _root_.solution (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 24 p ↔ (p.1 ≤ 0 ∧ p.2.1 < -1 ∧ p.2.2 < p.2.1) := Iff.rfl
end FourierJacobi.Analysis
