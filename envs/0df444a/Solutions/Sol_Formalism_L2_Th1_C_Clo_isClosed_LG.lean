-- Prove2me | solution 1 for Formalism.L2.Th1.C.Clo.isClosed_LG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:06:01.605464+00:00
-- url     : https://prove2.me/submissions/800dd4f6-16a2-403a-8c37-473065efac07

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_PhNormClosed
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_SecondCoeffConsistency
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Closure
import Theorems.Thm_Formalism_L2_Th1_C_Clo_CoeffCont_subst
import Theorems.Thm_Formalism_L2_Th1_C_Clo_isClosed_intMv

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
theorem _root_.solution [CharZero K] {R : Subring K} (hR : IsClosed (R : Set K))
    {f : T → MvPowerSeries σ K} (hf : CoeffCont f)
    (h0 : ∀ t, MvPowerSeries.constantCoeff (f t) = 0) : IsClosed {t | LG R (f t)} := by
  have : {t | LG R (f t)} = {t | IntMv R (mvExp (f t))} := by
    ext t
    exact ⟨fun h => h.2, fun h => ⟨h0 t, h⟩⟩
  rw [this]
  exact isClosed_intMv hR (hf.subst h0 _)
end Formalism.L2.Th1.C.Clo
