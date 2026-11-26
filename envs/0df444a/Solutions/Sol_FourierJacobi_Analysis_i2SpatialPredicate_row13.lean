-- Prove2me | solution 1 for FourierJacobi.Analysis.i2SpatialPredicate_row13
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:47:54.493203+00:00
-- url     : https://prove2.me/submissions/336c7565-5a97-43d7-8cf6-fe6c053ad13a

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Predicates

set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis
namespace FourierJacobi.Analysis
theorem _root_.solution (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 13 p ↔ (p.1 = -1 ∧ p.2.1 = -1 ∧ -1 ≤ p.2.2) := Iff.rfl
end FourierJacobi.Analysis
