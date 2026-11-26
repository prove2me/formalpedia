-- Prove2me | solution 1 for FourierJacobi.Analysis.i2DepthPredicate_row7
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:47:23.768217+00:00
-- url     : https://prove2.me/submissions/979ef100-d212-440c-97f1-2052d7c76a07

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Predicates

set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis
namespace FourierJacobi.Analysis
theorem _root_.solution (c : ℕ) : i2DepthPredicate 7 c ↔ (True) := Iff.rfl
end FourierJacobi.Analysis
