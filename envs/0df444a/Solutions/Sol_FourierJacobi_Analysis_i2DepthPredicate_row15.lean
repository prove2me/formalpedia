-- Prove2me | solution 1 for FourierJacobi.Analysis.i2DepthPredicate_row15
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:47:57.309844+00:00
-- url     : https://prove2.me/submissions/8bd0c7da-aab6-4153-9e61-5187a62a0a86

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Predicates

set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis
namespace FourierJacobi.Analysis
theorem _root_.solution (c : ℕ) : i2DepthPredicate 15 c ↔ (True) := Iff.rfl
end FourierJacobi.Analysis
