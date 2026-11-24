-- Prove2me | solution 1 for Formalism.NuclearRankWeightBounds.P.summable_psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:11:28.947076+00:00
-- url     : https://prove2.me/submissions/f4310b7d-d895-4498-ac43-ca5c76d75eff

import Definitions.Def_Formalism_LogSumExpBounds_StatementZ
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_LatSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.NuclearRankWeightBounds Formalism.NuclearRankWeightBounds.P
open Finset
namespace Formalism.NuclearRankWeightBounds.P
theorem _root_.solution : Summable psi := by
  have hnat : Summable (fun n : ℕ => (4 / ((n : ℝ) + 1)) ^ (5 / 4 : ℝ)) := by
    have h1 : Summable (fun n : ℕ => (((n : ℝ)) ^ (5 / 4 : ℝ))⁻¹) :=
      Real.summable_nat_rpow_inv.mpr (by norm_num)
    have h2 : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ (5 / 4 : ℝ))⁻¹) :=
      (summable_nat_add_iff 1).mpr h1
    have h3 := h2.mul_left ((4 : ℝ) ^ (5 / 4 : ℝ))
    refine h3.congr (fun n => ?_)
    have hn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    rw [Real.div_rpow (by norm_num) hn]
    push_cast
    ring
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · refine hnat.congr (fun n => ?_)
    simp [psi]
  · refine hnat.congr (fun n => ?_)
    simp [psi]
end Formalism.NuclearRankWeightBounds.P
