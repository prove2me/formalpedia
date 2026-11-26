-- Prove2me | solution 1 for FourierJacobi.Analysis.i2Case10Equiv_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:28:03.975964+00:00
-- url     : https://prove2.me/submissions/e4f83eba-c9da-4e56-9bb5-8f19a178f0db

import Definitions.Def_FourierJacobi_Valuations_Cartan
import Mathlib.Tactic.FinCases
import Definitions.Def_FourierJacobi_Analysis_I2Domains

set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace FourierJacobi.Analysis
theorem _root_.solution (n : ℕ × ℕ × ℕ) :
    (i2Case10Equiv n).val = (-(n.1 : ℤ), -(n.2.1 : ℤ)-2, -(n.2.1 : ℤ)-(n.2.2 : ℤ)-3) := rfl
end FourierJacobi.Analysis
