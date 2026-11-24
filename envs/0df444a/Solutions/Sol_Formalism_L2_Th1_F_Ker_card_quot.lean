-- Prove2me | solution 1 for Formalism.L2.Th1.F.Ker.card_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:37:41.962542+00:00
-- url     : https://prove2.me/submissions/e4a75284-e44e-4766-8a57-4b0c0fff3eb0

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_MulStableIntegral
import Theorems.Thm_Formalism_L2_Th1_F_Ker_mulEnd_injective
import Theorems.Thm_Formalism_L2_Th1_F_Ker_det_mulEnd

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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.Ker
namespace Formalism.L2.Th1.F.Ker
theorem _root_.solution (L : PeriodPair) (α : ℂ) (hα : α ≠ 0) (h : MulStable L α) :
    ((Nat.card (L.lattice ⧸ LinearMap.range (mulEnd L α h)) : ℕ) : ℝ) = Complex.normSq α := by
  haveI := Module.Free.of_basis L.latticeBasis
  haveI := Module.Finite.of_basis L.latticeBasis
  have key : (LinearMap.det (mulEnd L α h)).natAbs =
      Nat.card (L.lattice ⧸ LinearMap.range (mulEnd L α h)) := by
    rw [← Submodule.natAbs_det_equiv (LinearMap.range (mulEnd L α h))
      (LinearEquiv.ofInjective (mulEnd L α h) (mulEnd_injective L α hα h))]
    congr 2
  rw [← key, Nat.cast_natAbs, Int.cast_abs, det_mulEnd, abs_of_nonneg (Complex.normSq_nonneg α)]
end Formalism.L2.Th1.F.Ker
