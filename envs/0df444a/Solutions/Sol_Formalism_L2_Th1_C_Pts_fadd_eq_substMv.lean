-- Prove2me | solution 1 for Formalism.L2.Th1.C.Pts.fadd_eq_substMv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:34:41.328801+00:00
-- url     : https://prove2.me/submissions/34480609-20b9-4341-8992-287f3ffb7687

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IsotropicVanish
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Theorems.Thm_Formalism_L2_Th1_C_Pts_substMv_subst
import Theorems.Thm_Formalism_L2_Th1_C_Pts_constantCoeff_add_l

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
variable {K : Type} [Field K] {σ : Type} {l linv : PowerSeries K}
namespace Formalism.L2.Th1.C.Pts
theorem _root_.solution (h : IsLogPair l linv) {x y : MvPowerSeries σ K}
    (hx : MvPowerSeries.constantCoeff x = 0) (hy : MvPowerSeries.constantCoeff y = 0) :
    fadd l linv x y = MvPowerSeries.subst ![x, y]
      (fadd l linv (MvPowerSeries.X (0 : Fin 2)) (MvPowerSeries.X (1 : Fin 2))) := by
  have ha : ∀ s : Fin 2, MvPowerSeries.constantCoeff (![x, y] s) = 0 := by
    intro s
    fin_cases s
    · exact hx
    · exact hy
  have hs := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  have h0 : MvPowerSeries.constantCoeff (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) K) = 0 :=
    MvPowerSeries.constantCoeff_X 0
  have h1 : MvPowerSeries.constantCoeff (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K) = 0 :=
    MvPowerSeries.constantCoeff_X 1
  rw [fadd, fadd, substMv_subst (constantCoeff_add_l h h0 h1) ha, MvPowerSeries.subst_add hs,
    substMv_subst h0 ha, substMv_subst h1 ha, MvPowerSeries.subst_X hs, MvPowerSeries.subst_X hs]
  rfl
end Formalism.L2.Th1.C.Pts
