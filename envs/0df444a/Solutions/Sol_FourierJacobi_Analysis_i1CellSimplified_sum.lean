-- Prove2me | solution 1 for FourierJacobi.Analysis.i1CellSimplified_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:29:35.017576+00:00
-- url     : https://prove2.me/submissions/8f3e04c1-911e-4fc0-a622-0f6a4ea6d26a

import Definitions.Def_FourierJacobi_Analysis_I1Partition
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_I1Assembly
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
import Theorems.Thm_FourierJacobi_Analysis_i1r10DepthEquiv_val
import Theorems.Thm_FourierJacobi_Analysis_i1r10Equiv_val
import Theorems.Thm_FourierJacobi_Analysis_masterTerm_zero
import Theorems.Thm_FourierJacobi_Analysis_shellMonomial_zero
attribute [local simp] FourierJacobi.Analysis.i0NegativeRowEquiv_val
attribute [local simp] FourierJacobi.Analysis.i1r10DepthEquiv_val
attribute [local simp] FourierJacobi.Analysis.i1r10Equiv_val
attribute [local simp] FourierJacobi.Analysis.masterTerm_zero
attribute [local simp] FourierJacobi.Analysis.shellMonomial_zero



set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
open FourierJacobi.Algebra
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
namespace FourierJacobi.Analysis
theorem _root_.solution (t d U V T : ℂ) :
    (∑ i : Fin 17, i1CellSimplified t d U V T i) =
      ∑ i : Fin 15, i1StoredRows t d U V T i := by
  simp only [i1CellSimplified, i1StoredRows, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
  unfold regionTerm10 regionTerm11 regionTerm12 regionTerm13 regionTerm14 regionTerm15 regionTerm16 regionTerm17 regionTerm18 regionTerm19 regionTerm20 regionTerm21 regionTerm22 regionTerm23 regionTerm24
  simp only [pow_one]
  ring
end FourierJacobi.Analysis
