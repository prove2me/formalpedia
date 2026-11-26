-- Prove2me | solution 1 for FourierJacobi.Analysis.i2DepthPredicate_row21
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:48:40.073405+00:00
-- url     : https://prove2.me/submissions/52aae44b-63df-4b66-af67-a7d638e68c84

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Predicates

set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis
namespace FourierJacobi.Analysis
theorem _root_.solution (c : ℕ) : i2DepthPredicate 21 c ↔ (c = 1) := Iff.rfl
end FourierJacobi.Analysis
