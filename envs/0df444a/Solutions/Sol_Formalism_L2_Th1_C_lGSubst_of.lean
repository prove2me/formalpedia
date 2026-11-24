-- Prove2me | solution 1 for Formalism.L2.Th1.C.lGSubst_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:23:16.473796+00:00
-- url     : https://prove2.me/submissions/e725eee3-6ff3-479e-bdd8-e21811de2ea7

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IntBinomScalar
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_intMv_subst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open IntegralMvPolynomialLemmas
namespace Formalism.L2.Th1.C
theorem _root_.solution (hS : MvExpSubst) : LGSubst := by
  intro K _ _ R f hf σ a ha
  refine ⟨constantCoeff_subst_eq_zero ha.1 f hf.1, ?_⟩
  rw [← hS K σ f a hf.1 ha.1]
  exact intMv_subst (fun n => hf.2 _) ha
end Formalism.L2.Th1.C
