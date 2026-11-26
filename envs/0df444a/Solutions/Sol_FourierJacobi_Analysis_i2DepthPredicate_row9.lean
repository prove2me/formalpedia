-- Prove2me | solution 1 for FourierJacobi.Analysis.i2DepthPredicate_row9
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:47:27.144012+00:00
-- url     : https://prove2.me/submissions/3c522299-862f-427e-99dd-f429a0a9644f

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Predicates

set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis
namespace FourierJacobi.Analysis
theorem _root_.solution (c : ℕ) : i2DepthPredicate 9 c ↔ (True) := Iff.rfl
end FourierJacobi.Analysis
