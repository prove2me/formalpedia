-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.sharp_recursion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:57:20.813698+00:00
-- url     : https://prove2.me/submissions/0790d56f-8e92-424b-919d-7c4adf382917

import Definitions.Def_Formalism_HermitianCurvature_Statement
import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SharpRecursion
import Theorems.Thm_Formalism_FourierDecayAlt_P_Rec_Pp_sq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Rec_growth
import Theorems.Thm_Formalism_FourierDecayAlt_P_Rec_pow_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Real Formalism.FourierDecayAlt.P.Rec
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.RecursionSharp := by
  refine ⟨80, ?_⟩
  intro r a ε e σ ha ha2 hε hx he hσ hrec
  have hg := growth r a ε e σ (1 + ε + 2 * a) ha ha2 hε he hσ hrec le_rfl (r+1) le_rfl
  have hpb := pow_bound r a ε ha hε hx
  have hsq := pow_le_pow_left₀ (hσ (r+1)) hg 2
  have hPs := Pp_sq he (r+1)
  have hσ0 : 0 ≤ σ 0 ^ 2 := sq_nonneg _
  have hprod : 0 ≤ ∏ i ∈ Icc 1 (r + 1), (1 + e i) := by rw [← hPs]; exact sq_nonneg _
  calc σ (r+1) ^ 2 ≤ (Pp e (r+1) * (1 + ε + 2 * a) ^ (r+1) * σ 0) ^ 2 := hsq
    _ = ((1 + ε + 2 * a) ^ (r+1)) ^ 2 * (Pp e (r+1) ^ 2) * σ 0 ^ 2 := by ring
    _ = ((1 + ε + 2 * a) ^ (r+1)) ^ 2 * (∏ i ∈ Icc 1 (r + 1), (1 + e i)) * σ 0 ^ 2 := by
        rw [hPs]
    _ ≤ (1 + 80 * ((r : ℝ) + 1) * (ε + a)) * (∏ i ∈ Icc 1 (r + 1), (1 + e i)) * σ 0 ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ hσ0
        exact mul_le_mul_of_nonneg_right hpb hprod
end Formalism.FourierDecayAlt.P
