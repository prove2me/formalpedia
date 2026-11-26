-- Prove2me | solution 1 for FourierJacobi.Analysis.i2DepthPredicate_row3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:46:26.690589+00:00
-- url     : https://prove2.me/submissions/8e821350-096e-4dea-aaef-0014d2d59100

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Predicates

set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis
namespace FourierJacobi.Analysis
theorem _root_.solution (c : ℕ) : i2DepthPredicate 3 c ↔ (True) := Iff.rfl
end FourierJacobi.Analysis
