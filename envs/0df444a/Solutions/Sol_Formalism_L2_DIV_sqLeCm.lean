-- Prove2me | solution 1 for Formalism.L2.DIV.sqLeCm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:09:43.306328+00:00
-- url     : https://prove2.me/submissions/f91cab93-4c3b-4b0e-bc1d-ba4a9dce93a5

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ConjugationAtDistinguishedPlace
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_PowValCast
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoeffLemmas
import Theorems.Thm_Formalism_L2_DIV_conj_sqrt

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
theorem _root_.solution : SqLeCm := by
  intro ι m
  rw [sqQ, adjoin_le_iff]
  intro x hx τ
  have hτ : ∀ τ : Qb →+* ℂ, (τ x) ^ 2 = ((m : ℝ) : ℂ) := by
    intro τ
    rw [← map_pow, show x ^ 2 = (m : Qb) from hx, map_intCast]; push_cast; rfl
  by_cases hm : (m : ℝ) < 0
  · have hc : conjQb ι x = -x := by
      apply ι.injective
      rw [conjQb_spec, conj_sqrt (hτ ι), if_pos hm, map_neg]; ring
    rw [hc, conj_sqrt (hτ τ), if_pos hm, map_neg]; ring
  · have hc : conjQb ι x = x := by
      apply ι.injective
      rw [conjQb_spec, conj_sqrt (hτ ι), if_neg hm]; ring
    rw [hc, conj_sqrt (hτ τ), if_neg hm]; ring
end Formalism.L2.DIV
