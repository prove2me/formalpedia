-- Prove2me | solution 1 for Formalism.YangianSpanCharacter.P.gamma_ratio_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:42:20.552694+00:00
-- url     : https://prove2.me/submissions/690db1a2-6964-44a5-83ce-5404426a2229

import Definitions.Def_Formalism_YangianSpanCharacter_StatementE
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRTTProofs_SpanCharacterIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.YangianSpanCharacter Formalism.YangianSpanCharacter.P
open Finset
namespace Formalism.YangianSpanCharacter.P
theorem _root_.solution : Formalism.YangianSpanCharacter.E.GGRatio := by
  intro g hg k
  rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun i hi => ?_
  have hi1 : i ≠ 0 := by
    have := (Finset.mem_Ico.mp hi).1; omega
  have hgi : 1 < g ^ i := one_lt_pow₀ hg hi1
  have h0 : g ^ i ≠ 0 := by positivity
  have h1 : g ^ i - 1 ≠ 0 := by linarith
  have h2 : 1 - (g ^ i)⁻¹ ≠ 0 := by
    rw [sub_ne_zero]; intro h
    have : g ^ i = 1 := by rw [eq_comm, inv_eq_one] at h; exact h
    linarith
  field_simp
end Formalism.YangianSpanCharacter.P
