-- Prove2me | solution 1 for Formalism.L2.DIV.conj_ne_of_sq_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:35:53.903818+00:00
-- url     : https://prove2.me/submissions/6945186f-d34f-4f3d-9c4c-36e9f317d79c

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ConjugationAtDistinguishedPlace
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_PowValCast
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoeffLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.L2.Host Formalism.DivisionValues
namespace Formalism.L2.DIV
theorem _root_.solution {w : ℂ} {r : ℝ} (hr : r < 0) (hw : w ^ 2 = (r : ℂ)) : starRingEnd ℂ w ≠ w := by
  intro h
  obtain ⟨t, rfl⟩ := Complex.conj_eq_iff_real.1 h
  have : t ^ 2 = r := by exact_mod_cast hw
  nlinarith [sq_nonneg t]
end Formalism.L2.DIV
