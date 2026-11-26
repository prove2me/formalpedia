-- Prove2me | solution 1 for FourierJacobi.Analysis.i2DepthPredicate_row11
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:47:48.429906+00:00
-- url     : https://prove2.me/submissions/0fd85da0-aa31-4642-8e63-34dadb0f134a

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Predicates

set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis
namespace FourierJacobi.Analysis
theorem _root_.solution (c : ℕ) : i2DepthPredicate 11 c ↔ (True) := Iff.rfl
end FourierJacobi.Analysis
