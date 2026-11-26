-- Prove2me | solution 1 for FourierJacobi.Analysis.i2DepthPredicate_row0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:46:15.305927+00:00
-- url     : https://prove2.me/submissions/67f0ca29-d0d3-4b30-b279-c560f4aa4d3c

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Predicates

set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis
namespace FourierJacobi.Analysis
theorem _root_.solution (c : ℕ) : i2DepthPredicate 0 c ↔ (True) := Iff.rfl
end FourierJacobi.Analysis
