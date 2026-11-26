-- Prove2me | solution 1 for FourierJacobi.Analysis.i2RowTerm_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:11:33.644324+00:00
-- url     : https://prove2.me/submissions/6c42684f-4fee-499f-bd29-47ca039efaa6

import Definitions.Def_FourierJacobi_Analysis_I2Ambient
import Definitions.Def_FourierJacobi_Analysis_I2Partition
import Definitions.Def_FourierJacobi_Analysis_I2Master
import Theorems.Thm_FourierJacobi_Analysis_i2_partition_sum

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open scoped Classical
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
set_option linter.unusedVariables false
namespace FourierJacobi.Analysis
theorem _root_.solution (q t d U V T : ℂ) (p : LatticeIndex) :
    (∑ ν : Fin 25, i2RowTerm q t d U V T ν p) = masterTerm q t d U V T 2 p := by
  classical
  exact i2_partition_sum p.1 p.2.1 p.2.2.1 p.2.2.2 (masterTerm q t d U V T 2 p)
end FourierJacobi.Analysis
