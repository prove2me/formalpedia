-- Prove2me | solution 1 for Formalism.L2.Th1.F.LatOnly.tprod_submodule_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:25:02.712882+00:00
-- url     : https://prove2.me/submissions/4892df7d-fb40-40e1-84b8-84071b6247ad

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
    ∏' l : Λ, f (l : ℂ) = ∏' l : Λ', f (l : ℂ) := by
  subst h
  rfl
end Formalism.L2.Th1.F.LatOnly
