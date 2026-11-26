-- Prove2me | solution 1 for FourierJacobi.Analysis.i2DepthPredicate_row10
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:47:28.309354+00:00
-- url     : https://prove2.me/submissions/fb22a09e-df4b-4b71-baa1-2986dd5c05c4

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Predicates

set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis
namespace FourierJacobi.Analysis
theorem _root_.solution (c : ℕ) : i2DepthPredicate 10 c ↔ (True) := Iff.rfl
end FourierJacobi.Analysis
