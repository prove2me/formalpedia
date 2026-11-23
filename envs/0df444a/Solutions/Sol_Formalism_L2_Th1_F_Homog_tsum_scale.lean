-- Prove2me | solution 1 for Formalism.L2.Th1.F.Homog.tsum_scale
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:00:05.550372+00:00
-- url     : https://prove2.me/submissions/db6dbe36-2b31-4861-bcd7-1b9eda0ba4a5

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
open Formalism.L2.Th1.F.Homog
variable (L : PeriodPair) (c : ℂ) (hc : c ≠ 0)
namespace Formalism.L2.Th1.F.Homog
theorem _root_.solution (f : ℂ → ℂ) :
    ∑' l : (scalePair L c hc).lattice, f (l : ℂ) = ∑' l : L.lattice, f (c * (l : ℂ)) := (Equiv.tsum_eq (scaleEquiv L c hc) (fun l => f (l : ℂ))).symm
end Formalism.L2.Th1.F.Homog
