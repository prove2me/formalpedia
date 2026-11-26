-- Prove2me | solution 1 for FourierJacobi.Analysis.i2DepthPredicate_row1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:46:17.465102+00:00
-- url     : https://prove2.me/submissions/0c620ea1-f179-42cb-9149-1aa88cb32467

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Predicates

set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis
namespace FourierJacobi.Analysis
theorem _root_.solution (c : ℕ) : i2DepthPredicate 1 c ↔ (True) := Iff.rfl
end FourierJacobi.Analysis
