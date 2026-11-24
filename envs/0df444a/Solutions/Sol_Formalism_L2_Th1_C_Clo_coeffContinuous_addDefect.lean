-- Prove2me | solution 1 for Formalism.L2.Th1.C.Clo.coeffContinuous_addDefect
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:05:59.388815+00:00
-- url     : https://prove2.me/submissions/97a0afb6-2cc7-4754-b965-7b4618f259c8

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_PhNormClosed
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_SecondCoeffConsistency
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Closure
import Theorems.Thm_Formalism_L2_Th1_C_Clo_CoeffCont_const
import Theorems.Thm_Formalism_L2_Th1_C_Clo_CoeffCont_add
import Theorems.Thm_Formalism_L2_Th1_C_Clo_CoeffCont_sub
import Theorems.Thm_Formalism_L2_Th1_C_Clo_CoeffCont_subst
import Theorems.Thm_Formalism_L2_Th1_C_Clo_cc_fadd
import Theorems.Thm_Formalism_L2_Th1_C_Pts_constantCoeff_subst


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
open Finset
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open Formalism.L2.Th1.C.Clo
variable {K : Type} [Field K] {σ : Type}
variable [TopologicalSpace K] [IsTopologicalRing K] {T : Type} [TopologicalSpace T]
namespace Formalism.L2.Th1.C.Clo
theorem _root_.solution {l linv ph : PowerSeries K} (hl : PowerSeries.constantCoeff l = 0)
    (hli : PowerSeries.constantCoeff linv = 0)
    {x : MvPowerSeries σ K} (hx : MvPowerSeries.constantCoeff x = 0)
    {y : T → MvPowerSeries σ K} (hy : CoeffCont y)
    (hy0 : ∀ t, MvPowerSeries.constantCoeff (y t) = 0) :
    CoeffCont fun t => be0 l linv ph x (y t) := by
  have h1 : CoeffCont fun t => PowerSeries.subst x l + PowerSeries.subst (y t) l :=
    (CoeffCont.const _).add (hy.subst hy0 l)
  have h2 : CoeffCont fun t => fadd l linv x (y t) :=
    h1.subst (fun t => by
      rw [map_add, Pts.constantCoeff_subst hx hl, Pts.constantCoeff_subst (hy0 t) hl, add_zero]) linv
  exact ((h2.subst (fun t => cc_fadd hl hli hx (hy0 t)) ph).sub (CoeffCont.const _)).sub
    (hy.subst hy0 ph)
end Formalism.L2.Th1.C.Clo
