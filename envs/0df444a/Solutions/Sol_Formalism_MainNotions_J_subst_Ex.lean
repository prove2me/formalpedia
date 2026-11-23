-- Prove2me | solution 1 for Formalism.MainNotions.J.subst_Ex
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:24:55.422947+00:00
-- url     : https://prove2.me/submissions/af2e3c68-d570-4842-94a3-999b81cef4cb

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_AdmissibleParameterJoins_GandSo
import Theorems.Thm_Formalism_MainNotions_J_subst_psubst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.J
open MvPowerSeries
variable {ι κ : Type} {K K' : Type} [Field K] [CharZero K] [Field K'] [CharZero K']
namespace Formalism.MainNotions.J
theorem _root_.solution {c : ι → MvPowerSeries κ K} (hc : HasSubst c) {f : MvPowerSeries ι K}
    (hf : constantCoeff f = 0) : subst c (Ex f) = Ex (subst c f) := by
  exact subst_psubst hc hf (PowerSeries.exp K)
end Formalism.MainNotions.J
