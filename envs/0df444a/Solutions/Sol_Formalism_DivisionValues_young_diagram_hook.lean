-- Prove2me | solution 1 for Formalism.DivisionValues.young_diagram_hook
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:00.39259+00:00
-- url     : https://prove2.me/submissions/018c4a5a-e85d-4ac9-946a-0b009566fc72

import Definitions.Def_Formalism_QuotientMetricDivisors_TheoremDivIneqRows
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SumInterlacedBoundFails
import Definitions.Def_Formalism_LogFactorialIndices_SubspaceIndexSigned
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_YoungDiagramHook
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset
noncomputable section
namespace Formalism.DivisionValues
open Formalism.LatticeIndexTer (ph)
namespace W8
end W8
open W8
private lemma prod_range_sub_eq_factorial' (n : ℕ) : ∏ j ∈ Finset.range n, (n - j) = n.factorial := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ', Nat.factorial_succ]
    have h : ∀ j ∈ Finset.range k, k + 1 - (j + 1) = k - j := fun j _ => by omega
    rw [Finset.prod_congr rfl h, ih, Nat.sub_zero]
    ring
namespace W8
end W8
end Formalism.DivisionValues
end
end

set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.LatticeIndexTer (ph)
open W8
namespace Formalism.DivisionValues
theorem _root_.solution : RowsHook := by
  intro μ
  have hcell : ∀ p : ℕ × ℕ, p ∈ μ.cells ↔
      p.1 ∈ Finset.range (μ.colLen 0) ∧ p.2 ∈ Finset.range (μ.rowLen p.1) := by
    rintro ⟨i, j⟩
    simp only [YoungDiagram.mem_cells, Finset.mem_range]
    constructor
    · intro h
      exact ⟨YoungDiagram.mem_iff_lt_colLen.mp (μ.up_left_mem le_rfl (Nat.zero_le j) h),
        YoungDiagram.mem_iff_lt_rowLen.mp h⟩
    · intro h
      exact YoungDiagram.mem_iff_lt_rowLen.mpr h.2
  have hle : ∏ x ∈ μ.cells, (μ.rowLen x.1 - x.2) ≤ Formalism.LatticeIndexTer.hookProd μ := by
    unfold Formalism.LatticeIndexTer.hookProd
    apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
    rintro ⟨i, j⟩ h
    have h1 : i < μ.colLen j := YoungDiagram.mem_iff_lt_colLen.mp h
    show μ.rowLen i - j ≤ μ.rowLen i - j + (μ.colLen j - i) - 1
    omega
  have heq : ∏ x ∈ μ.cells, (μ.rowLen x.1 - x.2) =
      ∏ i ∈ Finset.range (μ.colLen 0), (μ.rowLen i).factorial := by
    rw [Finset.prod_finset_product μ.cells (Finset.range (μ.colLen 0))
      (fun i => Finset.range (μ.rowLen i)) hcell]
    exact Finset.prod_congr rfl fun i _ => prod_range_sub_eq_factorial' (μ.rowLen i)
  have hpos : 0 < ∏ i ∈ Finset.range (μ.colLen 0), (μ.rowLen i).factorial :=
    Finset.prod_pos fun i _ => Nat.factorial_pos _
  have hlog : logFactRows (μ.rowLens : Multiset ℕ) =
      ∑ i ∈ Finset.range (μ.colLen 0), Real.log ((μ.rowLen i).factorial : ℝ) := by
    unfold logFactRows YoungDiagram.rowLens
    rw [Multiset.map_coe, List.map_map]
    rfl
  rw [hlog, ← Real.log_prod (s := Finset.range (μ.colLen 0))
    (f := fun i => ((μ.rowLen i).factorial : ℝ))
    (fun i _ => (Nat.cast_pos.mpr (Nat.factorial_pos _)).ne'),
    ← Nat.cast_prod]
  apply Real.log_le_log (by exact_mod_cast hpos)
  exact_mod_cast heq.symm.le.trans hle
end Formalism.DivisionValues
