-- Prove2me | solution 1 for FourierJacobi.Analysis.i2DepthPredicate_row23
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:48:52.227335+00:00
-- url     : https://prove2.me/submissions/c97128a0-fff4-4d0b-8666-b28e5af45279

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Predicates

set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis
namespace FourierJacobi.Analysis
theorem _root_.solution (c : ℕ) : i2DepthPredicate 23 c ↔ (True) := Iff.rfl
end FourierJacobi.Analysis
