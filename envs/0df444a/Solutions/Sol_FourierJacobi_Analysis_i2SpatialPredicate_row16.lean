-- Prove2me | solution 1 for FourierJacobi.Analysis.i2SpatialPredicate_row16
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:48:00.68288+00:00
-- url     : https://prove2.me/submissions/3020bac9-e95f-4a9b-bd0f-ec6d7ec570bc

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Predicates

set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis
namespace FourierJacobi.Analysis
theorem _root_.solution (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 16 p ↔ (p.1 ≤ -2 ∧ p.2.1 = -1 ∧ -1 ≤ p.2.2) := Iff.rfl
end FourierJacobi.Analysis
