-- Prove2me | solution 1 for FourierJacobi.Analysis.i2RegionTerm_eq_regionTerms
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:50:29.325785+00:00
-- url     : https://prove2.me/submissions/df631b69-5a43-4906-ab6f-90d1b673d8a4

import Definitions.Def_FourierJacobi_Analysis_I2Assembly
import Mathlib.Data.Fintype.Fin
import Definitions.Def_FourierJacobi_Analysis_I2Ambient

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open scoped Classical
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
set_option linter.unusedVariables false
namespace FourierJacobi.Analysis
theorem _root_.solution (t d U V : ℂ) (ν : Fin 25) :
    i2RegionTerm ν t d U V = Algebra.regionTerms t d U V (i2Offset ν) := by
  fin_cases ν <;> rfl
end FourierJacobi.Analysis
