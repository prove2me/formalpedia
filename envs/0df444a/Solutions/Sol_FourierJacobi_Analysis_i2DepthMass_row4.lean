-- Prove2me | solution 1 for FourierJacobi.Analysis.i2DepthMass_row4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:36:05.270445+00:00
-- url     : https://prove2.me/submissions/8560e9e1-20f4-4d65-b0e1-0ec150d39c2b

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Convergence
import Definitions.Def_FourierJacobi_Analysis_I2Complete

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace FourierJacobi.Analysis
theorem _root_.solution (q : ℂ) : i2DepthMass q 4 = (q - 2) / (q - 1) := rfl
end FourierJacobi.Analysis
