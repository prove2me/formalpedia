-- Prove2me | solution 1 for FourierJacobi.Analysis.i2DepthPredicate_row4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:46:27.70912+00:00
-- url     : https://prove2.me/submissions/ade3c236-e10d-4896-8e97-8102c7c9a9c5

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Predicates

set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis
namespace FourierJacobi.Analysis
theorem _root_.solution (c : ℕ) : i2DepthPredicate 4 c ↔ (c = 0) := Iff.rfl
end FourierJacobi.Analysis
