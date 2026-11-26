-- Prove2me | solution 1 for FourierJacobi.Analysis.i1CellValue_sum_eq_regions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:31:39.5234+00:00
-- url     : https://prove2.me/submissions/96dd4fd2-14fa-49fc-9596-91a2aff9e8ff

import Definitions.Def_FourierJacobi_Analysis_I1Partition
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_I1Assembly
import Theorems.Thm_FourierJacobi_Analysis_i1StoredRows_eq_regionTerms
import Theorems.Thm_FourierJacobi_Analysis_i1CellValue_eq_simplified
import Theorems.Thm_FourierJacobi_Analysis_i1CellSimplified_sum

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
theorem _root_.solution (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hqt : q*t^2=1)
    (h : GeometricRange t d U V T) :
    (∑ i : Fin 17, i1CellValue q t d U V T i) =
      ∑ i : Fin 15, regionTerms t d (T*U) (T*V) ⟨10+i.val, by omega⟩ := by
  calc
    _ = ∑ i : Fin 17, i1CellSimplified t d U V T i := by
      apply Finset.sum_congr rfl
      intro i hi
      exact i1CellValue_eq_simplified q t d U V T ht hd hqt h i
    _ = ∑ i : Fin 15, i1StoredRows t d U V T i := i1CellSimplified_sum t d U V T
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      exact i1StoredRows_eq_regionTerms t d U V T i
end FourierJacobi.Analysis
