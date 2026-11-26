-- Prove2me | solution 1 for FourierJacobi.Analysis.i2SpatialPredicate_row20
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:48:25.521476+00:00
-- url     : https://prove2.me/submissions/9f234fc9-9f09-4078-ba67-1249cb43269e

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Predicates

set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis
namespace FourierJacobi.Analysis
theorem _root_.solution (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 20 p ↔ (p.1 ≤ 0 ∧ p.2.1 < -1 ∧ p.2.1 ≤ p.2.2 ∧ 2*p.2.2 = p.2.1-2) := Iff.rfl
end FourierJacobi.Analysis
