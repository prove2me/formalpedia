-- Prove2me | solution 1 for Formalism.L2.Th1.C.Pts.isPt_flin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:37:39.551565+00:00
-- url     : https://prove2.me/submissions/a2746de5-0cd7-449d-bc49-3f27bebbc5da

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IsotropicVanish
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Theorems.Thm_Formalism_L2_Th1_C_Pts_subst_l_linv
import Theorems.Thm_Formalism_L2_Th1_C_Pts_constantCoeff_C_mul_l
import Theorems.Thm_Formalism_L2_Th1_C_Pts_l_fmul
import Theorems.Thm_Formalism_L2_Th1_C_Pts_isPt_fadd
import Theorems.Thm_Formalism_L2_Th1_C_Pts_isPt_fmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open Formalism.L2.Th1.C.Pts
open IntegralMvPolynomialLemmas
variable {K : Type} [Field K] {σ : Type} {R : Subring K} {l linv : PowerSeries K}
namespace Formalism.L2.Th1.C.Pts
theorem _root_.solution (h : IsLogPair l linv) (hF : FGInt R l linv) {n : Type} [Fintype n]
    {c : n → K} (hc : ∀ j, EndInt R l linv (c j)) {u : n → MvPowerSeries σ K}
    (hu : ∀ j, IsPt R (u j)) : IsPt R (flin l linv c u) := by
  classical
  have key : ∀ s : Finset n, IsPt R
      (PowerSeries.subst (∑ j ∈ s, MvPowerSeries.C (c j) * PowerSeries.subst (u j) l) linv) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty, PowerSeries.subst_zero_of_constantCoeff_zero h.2.2.1]
      exact ⟨map_zero _, fun _ => by rw [map_zero]; exact R.zero_mem⟩
    | insert j s hj ih =>
      have h0 : MvPowerSeries.constantCoeff
          (∑ j ∈ s, MvPowerSeries.C (c j) * PowerSeries.subst (u j) l) = 0 := by
        rw [map_sum]
        exact Finset.sum_eq_zero fun j _ => constantCoeff_C_mul_l h (c j) (hu j).1
      have := isPt_fadd h hF (isPt_fmul h (hc j) (hu j)) ih
      rw [fadd, l_fmul h (c j) (hu j).1, subst_l_linv h h0] at this
      rw [Finset.sum_insert hj]
      exact this
  exact key Finset.univ
end Formalism.L2.Th1.C.Pts
