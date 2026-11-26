-- Prove2me | solution 1 for FourierJacobi.Analysis.i2DepthPredicate_row18
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:48:23.318266+00:00
-- url     : https://prove2.me/submissions/1eb496c1-03bb-4703-a8de-01bef83435e1

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Predicates

set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis
namespace FourierJacobi.Analysis
theorem _root_.solution (c : ℕ) : i2DepthPredicate 18 c ↔ (True) := Iff.rfl
end FourierJacobi.Analysis
