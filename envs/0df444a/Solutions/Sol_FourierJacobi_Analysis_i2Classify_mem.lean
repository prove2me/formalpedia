-- Prove2me | solution 1 for FourierJacobi.Analysis.i2Classify_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:07:30.543337+00:00
-- url     : https://prove2.me/submissions/8ecf9b8a-c488-451e-a16f-05188239d427

import Definitions.Def_FourierJacobi_Analysis_I2Predicates
import Mathlib.Data.Fintype.Fin
import Definitions.Def_FourierJacobi_Analysis_I2Partition

set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace FourierJacobi.Analysis
theorem _root_.solution (k j h : ℤ) (c : ℕ) :
    i2SpatialPredicate (i2Classify k j h c) (k,j,h) ∧
      i2DepthPredicate (i2Classify k j h c) c := by
  unfold i2Classify i2TailClassify
  split_ifs <;> norm_num [i2SpatialPredicate, i2DepthPredicate] at * <;> omega
end FourierJacobi.Analysis
