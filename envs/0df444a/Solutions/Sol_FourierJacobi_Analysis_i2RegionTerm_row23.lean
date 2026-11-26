-- Prove2me | solution 1 for FourierJacobi.Analysis.i2RegionTerm_row23
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:42:47.612839+00:00
-- url     : https://prove2.me/submissions/21457d2a-fc8b-4429-85b8-e3e76d90ad7e

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
theorem _root_.solution (t d U V : ℂ) :
    i2RegionTerm 23 t d U V = Algebra.regionTerm48 t d U V
      (1 - d * V * t) (1 - V * t / d) (1 - V ^ 2 * t ^ 2)
      (1 - U * t ^ 2) (1 - U * t ^ 4) := rfl
end FourierJacobi.Analysis
