-- Prove2me | solution 1 for Formalism.L2.Th1.H.lineRestr_hasSubst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:27:28.992936+00:00
-- url     : https://prove2.me/submissions/7f086c53-678f-474e-a3c7-a69c5dfcbf02

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_TaylorMvLinear
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_IteratedDerivLine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
namespace Formalism.L2.Th1.H
theorem _root_.solution {K : Type*} [CommRing K] {n : Type*} [Finite n] (v : n → K) :
    MvPowerSeries.HasSubst (fun i => (PowerSeries.C (v i) * PowerSeries.X : PowerSeries K)) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by
    have : PowerSeries.constantCoeff (PowerSeries.C (v i) * PowerSeries.X : PowerSeries K) = 0 := by simp
    exact this
end Formalism.L2.Th1.H
