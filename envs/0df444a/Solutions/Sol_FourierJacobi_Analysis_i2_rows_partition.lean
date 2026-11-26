-- Prove2me | solution 1 for FourierJacobi.Analysis.i2_rows_partition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:08:39.912988+00:00
-- url     : https://prove2.me/submissions/1a836439-c0dc-43eb-bbb7-6e32d361e1d5

import Definitions.Def_FourierJacobi_Analysis_I2Predicates
import Mathlib.Data.Fintype.Fin
import Definitions.Def_FourierJacobi_Analysis_I2Partition
import Theorems.Thm_FourierJacobi_Analysis_i2Classify_mem
import Theorems.Thm_FourierJacobi_Analysis_i2Classify_eq_of_mem

set_option autoImplicit false
open FourierJacobi FourierJacobi.Analysis
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace FourierJacobi.Analysis
theorem _root_.solution (k j h : ℤ) (c : ℕ) :
    ∃! ν : Fin 25, i2SpatialPredicate ν (k,j,h) ∧ i2DepthPredicate ν c := by
  refine ⟨i2Classify k j h c, i2Classify_mem k j h c, ?_⟩
  intro ν hν
  exact (i2Classify_eq_of_mem ν k j h c hν.1 hν.2).symm
end FourierJacobi.Analysis
