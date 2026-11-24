-- Prove2me | solution 1 for Formalism.LT.TorsProof.norm_sum_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:19:07.577558+00:00
-- url     : https://prove2.me/submissions/991cd270-2f14-4e85-beaf-2a28defa0a28

import Definitions.Def_Formalism_TorsionNormIteration_Statement
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_TorsionNormIterProof

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open Formalism Formalism.LT Formalism.LT.TorsProof
open Polynomial
variable {K : Type*} [NormedField K] [IsUltrametricDist K]
namespace Formalism.LT.TorsProof
theorem _root_.solution {s : Finset ℕ} {f : ℕ → K} {c : ℝ} (hc : 0 < c)
    (h : ∀ i ∈ s, ‖f i‖ < c) : ‖∑ i ∈ s, f i‖ < c := by
  rcases s.eq_empty_or_nonempty with hs | hs
  · simp [hs, hc]
  · obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hs f
    exact hle.trans_lt (h i hi)
end Formalism.LT.TorsProof
