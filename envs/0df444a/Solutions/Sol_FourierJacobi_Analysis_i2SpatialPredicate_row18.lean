-- Prove2me | solution 1 for FourierJacobi.Analysis.i2SpatialPredicate_row18
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:48:22.782369+00:00
-- url     : https://prove2.me/submissions/16d9de35-2ba7-43f5-88d4-461ae34bfbf8

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Predicates

set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis
namespace FourierJacobi.Analysis
theorem _root_.solution (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 18 p ↔ (p.1 ≤ -1 ∧ 0 ≤ p.2.1 ∧ p.2.2 ≤ -1) := Iff.rfl
end FourierJacobi.Analysis
