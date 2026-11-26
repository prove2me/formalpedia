-- Prove2me | solution 1 for FourierJacobi.Analysis.i2DepthPredicate_row22
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:48:51.133304+00:00
-- url     : https://prove2.me/submissions/68e0947d-7446-432d-901f-1d0837ec84c6

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Predicates

set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis
namespace FourierJacobi.Analysis
theorem _root_.solution (c : ℕ) : i2DepthPredicate 22 c ↔ (2 ≤ c) := Iff.rfl
end FourierJacobi.Analysis
