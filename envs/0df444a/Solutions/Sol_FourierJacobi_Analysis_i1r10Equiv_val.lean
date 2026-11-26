-- Prove2me | solution 1 for FourierJacobi.Analysis.i1r10Equiv_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:22:25.892803+00:00
-- url     : https://prove2.me/submissions/94aac11c-978b-492b-905e-50fc1e2df9ac

import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Definitions.Def_FourierJacobi_Analysis_I1Complete

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
namespace FourierJacobi.Analysis
theorem _root_.solution (a b c : ℕ) :
    (i1r10Equiv (a,b,c)).val = (-(a : ℤ),-(b : ℤ)-1,-(b : ℤ)-(c : ℤ)-2) := rfl
end FourierJacobi.Analysis
