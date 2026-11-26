-- Prove2me | solution 1 for FourierJacobi.Analysis.i2DepthPredicate_row13
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:47:54.950685+00:00
-- url     : https://prove2.me/submissions/de4d555b-0e56-4a28-8c00-ff4fd168ed29

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Predicates

set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis
namespace FourierJacobi.Analysis
theorem _root_.solution (c : ℕ) : i2DepthPredicate 13 c ↔ (True) := Iff.rfl
end FourierJacobi.Analysis
