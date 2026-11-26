-- Prove2me | solution 1 for FourierJacobi.Analysis.i2DepthPredicate_row20
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:48:26.129597+00:00
-- url     : https://prove2.me/submissions/0842f66f-82bf-4897-8f5f-9df00610ee14

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Predicates

set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis
namespace FourierJacobi.Analysis
theorem _root_.solution (c : ℕ) : i2DepthPredicate 20 c ↔ (c = 0) := Iff.rfl
end FourierJacobi.Analysis
