-- Prove2me | solution 1 for Formalism.L2.Th1.F.LatOnly.tsum_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:59:38.27872+00:00
-- url     : https://prove2.me/submissions/e55dbb28-d0c8-41e8-aa6e-8b99ebb90f60

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_LatticeOnly

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
open Formalism.L2.Th1.F.LatOnly
namespace Formalism.L2.Th1.F.LatOnly
theorem _root_.solution {Λ Λ' : Submodule ℤ ℂ} (h : Λ = Λ') (f : ℂ → ℂ) :
    ∑' l : Λ, f (l : ℂ) = ∑' l : Λ', f (l : ℂ) := by
  subst h
  rfl
end Formalism.L2.Th1.F.LatOnly
