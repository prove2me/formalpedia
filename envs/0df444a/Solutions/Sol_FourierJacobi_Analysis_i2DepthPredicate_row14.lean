-- Prove2me | solution 1 for FourierJacobi.Analysis.i2DepthPredicate_row14
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:47:56.29538+00:00
-- url     : https://prove2.me/submissions/ceb2162e-e448-4426-9f81-24823ce7febb

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Predicates

set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis
namespace FourierJacobi.Analysis
theorem _root_.solution (c : ℕ) : i2DepthPredicate 14 c ↔ (True) := Iff.rfl
end FourierJacobi.Analysis
