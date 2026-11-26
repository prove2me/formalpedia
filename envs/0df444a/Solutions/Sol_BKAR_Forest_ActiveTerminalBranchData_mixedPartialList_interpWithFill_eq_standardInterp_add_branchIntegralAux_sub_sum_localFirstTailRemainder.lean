-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.mixedPartialList_interpWithFill_eq_standardInterp_add_branchIntegralAux_sub_sum_localFirstTailRemainder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:41:49.80895+00:00
-- url     : https://prove2.me/submissions/c4fdc709-a57c-42e7-896b-7f37f0e36765

import Definitions.Def_BKAR_CubePartition_Prefixed
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_branchIntegralAux_eq_sum_activeExtension_integrals_add_sum_localFirstTailRemainder
import Theorems.Thm_BKAR_Forest_mixedPartialList_interpWithFill_eq_standardInterp_add_sum_activeExtensions


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveTerminalBranchData
variable {F : Forest V}
namespace BKAR.Forest.ActiveTerminalBranchData
theorem _root_.solution
    (data : ActiveTerminalBranchData F)
    (es : List (Edge V)) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) (b : ℝ)
    (hbound : ∀ t ∈ Set.uIcc 0 b, ∀ e : F.EdgeParam, t ≤ u e)
    (hρ : ∀ t ∈ Set.uIcc 0 b,
      DifferentiableAt ℝ (mixedPartialList es ρ) (F.interpWithFill u t))
    (hint : ∀ e ∈ F.activeEdges,
      IntervalIntegrable
        (fun t : ℝ => mixedPartialList (e :: es) ρ
          (F.interpWithFill u t))
        MeasureTheory.volume 0 b) :
    mixedPartialList es ρ (F.interpWithFill u b) =
      mixedPartialList es ρ (F.standardInterp u) +
        data.branchIntegralAux b u (mixedPartialList es ρ) -
          Finset.sum F.activeEdges.attach
            (fun e => data.localFirstTailRemainder e b u es ρ) := by
  have hstep :=
    F.mixedPartialList_interpWithFill_eq_standardInterp_add_sum_activeExtensions
      es u ρ b hbound hρ hint data.extension
  have hbranch :=
    data.branchIntegralAux_eq_sum_activeExtension_integrals_add_sum_localFirstTailRemainder
      b u es ρ
  linarith
end BKAR.Forest.ActiveTerminalBranchData
