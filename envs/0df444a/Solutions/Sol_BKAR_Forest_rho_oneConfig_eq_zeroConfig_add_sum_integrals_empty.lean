-- Prove2me | solution 1 for BKAR.Forest.rho_oneConfig_eq_zeroConfig_add_sum_integrals_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:16:50.140205+00:00
-- url     : https://prove2.me/submissions/e0c4bb97-2256-42b5-8d77-ba7a6fdb9de3

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_BKAR_ForestGraph
import Definitions.Def_BKAR_Differential
import Definitions.Def_BKAR_OrderedExpansion
import Theorems.Thm_BKAR_Forest_rho_interpWithFill_eq_standardInterp_add_sum_integrals_activeEdges
import Theorems.Thm_BKAR_Forest_emptyParam_interpWithFill
import Theorems.Thm_BKAR_Forest_emptyParam_interpWithFill_one
import Theorems.Thm_BKAR_Forest_emptyParam_standardInterp


set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (ρ : (Edge V → ℝ) → ℝ)
    (hρ : ∀ t ∈ Set.uIcc 0 (1 : ℝ),
      DifferentiableAt ℝ ρ (constantConfig t))
    (hint : ∀ e : Edge V,
      IntervalIntegrable
        (fun t : ℝ => partialDeriv e ρ (constantConfig t))
        MeasureTheory.volume 0 1) :
    ρ oneConfig =
      ρ zeroConfig +
        Finset.sum (Finset.univ : Finset (Edge V))
          (fun e => ∫ t in 0..(1 : ℝ),
            partialDeriv e ρ (constantConfig t)) := by
  have hbase :
      ρ ((Forest.empty V).interpWithFill emptyParam 1) =
        ρ ((Forest.empty V).standardInterp emptyParam) +
          Finset.sum (Forest.empty V).activeEdges
            (fun e => ∫ t in 0..(1 : ℝ),
              partialDeriv e ρ
                ((Forest.empty V).interpWithFill emptyParam t)) :=
    (Forest.empty V).rho_interpWithFill_eq_standardInterp_add_sum_integrals_activeEdges
      emptyParam ρ 1
      (by
        intro t ht
        rw [emptyParam_interpWithFill t]
        exact hρ t ht)
      (by
        intro e _
        have hfun :
            (fun t : ℝ =>
                partialDeriv e ρ
                  ((Forest.empty V).interpWithFill emptyParam t)) =
              fun t : ℝ => partialDeriv e ρ (constantConfig t) := by
          funext t
          rw [emptyParam_interpWithFill t]
        rw [hfun]
        exact hint e)
  rw [emptyParam_interpWithFill_one, emptyParam_standardInterp,
    empty_activeEdges] at hbase
  have hsum :
      Finset.sum (Finset.univ : Finset (Edge V))
          (fun e => ∫ t in 0..(1 : ℝ),
            partialDeriv e ρ
              ((Forest.empty V).interpWithFill emptyParam t)) =
        Finset.sum (Finset.univ : Finset (Edge V))
          (fun e => ∫ t in 0..(1 : ℝ),
            partialDeriv e ρ (constantConfig t)) := by
    apply Finset.sum_congr rfl
    intro e _
    apply intervalIntegral.integral_congr
    intro t _
    change partialDeriv e ρ
        ((Forest.empty V).interpWithFill emptyParam t) =
      partialDeriv e ρ (constantConfig t)
    rw [emptyParam_interpWithFill t]
  rw [hsum] at hbase
  exact hbase
end BKAR.Forest
