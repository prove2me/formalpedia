-- Prove2me | solution 1 for FourierJacobi.Analysis.i2SpatialPredicate_row15
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:47:56.737912+00:00
-- url     : https://prove2.me/submissions/1aee1820-6f0c-4363-9e6e-a51d5cfcbedc

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Predicates

set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis
namespace FourierJacobi.Analysis
theorem _root_.solution (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 15 p ↔ (p.1 ≤ -2 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2) := Iff.rfl
end FourierJacobi.Analysis
