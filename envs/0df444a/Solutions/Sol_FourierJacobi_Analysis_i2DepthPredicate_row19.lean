-- Prove2me | solution 1 for FourierJacobi.Analysis.i2DepthPredicate_row19
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:48:24.427992+00:00
-- url     : https://prove2.me/submissions/a1ca68f4-207e-418d-a770-c2922b5472b5

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Predicates

set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis
namespace FourierJacobi.Analysis
theorem _root_.solution (c : ℕ) : i2DepthPredicate 19 c ↔ (True) := Iff.rfl
end FourierJacobi.Analysis
