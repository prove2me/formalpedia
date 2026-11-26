-- Prove2me | solution 1 for FourierJacobi.Analysis.i2DepthPredicate_row17
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:48:22.247706+00:00
-- url     : https://prove2.me/submissions/d6c87fd3-c1c5-41dc-a6d1-7f1ec254b94f

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Predicates

set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis
namespace FourierJacobi.Analysis
theorem _root_.solution (c : ℕ) : i2DepthPredicate 17 c ↔ (True) := Iff.rfl
end FourierJacobi.Analysis
