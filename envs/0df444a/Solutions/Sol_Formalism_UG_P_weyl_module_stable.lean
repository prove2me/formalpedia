-- Prove2me | solution 1 for Formalism.UG.P.weyl_module_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:43:41.269056+00:00
-- url     : https://prove2.me/submissions/c90fc341-a2e2-407a-941c-a7865c83fe0a

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_LinSubstIsHomogeneous
import Theorems.Thm_Formalism_UG_P_polyAct_weyl_gen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open Formalism Formalism.UG Formalism.UG.P
variable {O : Type} [CommRing O] {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution : Formalism.UG.WeylStable := by
  intro O _ n _ _ k g P hP
  have hle : weylSub O n k ≤ (weylSub O n k).comap (polyAct O n g).toLinearMap := by
    refine Submodule.span_le.mpr ?_
    rintro p ⟨α, hα, rfl⟩
    exact polyAct_weyl_gen g k α hα
  exact hle hP
end Formalism.UG.P
