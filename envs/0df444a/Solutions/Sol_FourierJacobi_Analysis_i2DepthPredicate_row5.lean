-- Prove2me | solution 1 for FourierJacobi.Analysis.i2DepthPredicate_row5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:46:42.892863+00:00
-- url     : https://prove2.me/submissions/babecd96-92ea-45b3-9b4f-d3dc98892a97

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Predicates

set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis
namespace FourierJacobi.Analysis
theorem _root_.solution (c : ℕ) : i2DepthPredicate 5 c ↔ (c = 1) := Iff.rfl
end FourierJacobi.Analysis
