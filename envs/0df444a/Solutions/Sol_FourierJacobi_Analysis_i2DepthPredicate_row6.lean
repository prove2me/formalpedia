-- Prove2me | solution 1 for FourierJacobi.Analysis.i2DepthPredicate_row6
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:47:21.1228+00:00
-- url     : https://prove2.me/submissions/d6a5894d-dbef-4bf9-9efc-0aa45cad2741

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Predicates

set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis
namespace FourierJacobi.Analysis
theorem _root_.solution (c : ℕ) : i2DepthPredicate 6 c ↔ (2 ≤ c) := Iff.rfl
end FourierJacobi.Analysis
