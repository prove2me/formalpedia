-- Prove2me | solution 1 for FourierJacobi.Analysis.i2RegionTerm_row0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:34:58.157028+00:00
-- url     : https://prove2.me/submissions/87a0a913-ebc8-44b9-8587-c47f2182ae85

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
    i2RegionTerm 0 t d U V = Algebra.regionTerm25 t d U V
      (1 - d * V * t) (1 - V * t / d) (1 - V ^ 2 * t ^ 2)
      (1 - U * t ^ 2) (1 - U * t ^ 4) := rfl
end FourierJacobi.Analysis
