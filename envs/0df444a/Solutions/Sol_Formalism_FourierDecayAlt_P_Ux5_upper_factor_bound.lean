-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux5.upper_factor_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:11:12.73504+00:00
-- url     : https://prove2.me/submissions/4bddb0f2-0fe7-4455-b459-a4522701bf18

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DetNormLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_pow_le_of_lb
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_ldu_upper_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux5
namespace Formalism.FourierDecayAlt.P.Ux5
theorem _root_.solution {p : ℕ} (L U : Matrix (Fin p) (Fin p) ℂ) (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0)
    (hL : ∀ a b, a < b → L a b = 0) (hL1 : ∀ a, L a a = 1) (hU : ∀ a b, b < a → U a b = 0)
    (hU1 : ∀ a, U a a = 1) {m δ : ℝ} (hm : 0 ≤ m) (hδ : 0 < δ) (hδm : δ ≤ m ^ p)
    (hM : EB (L * diagonal d * U) m) (i j' : Fin p) :
    ‖U i j'‖ ≤ (∑ i : Fin p, ((i.val + 1).factorial : ℝ) / ‖∏ t : Fin (i.val + 1), d (Fin.castLE i.isLt t)‖) *
      ((1 + δ⁻¹) * m ^ p) := by
  have h1 := ldu_upper_bound L U d hL hL1 hU hU1 hM i j'
  have hP : 0 < ‖∏ t : Fin (i.val + 1), d (Fin.castLE i.isLt t)‖ :=
    norm_pos_iff.mpr (Finset.prod_ne_zero_iff.mpr fun t _ => hd _)
  rw [norm_mul] at h1
  have h2 : ‖U i j'‖ ≤ ((i.val + 1).factorial : ℝ) / ‖∏ t : Fin (i.val + 1), d (Fin.castLE i.isLt t)‖ *
      m ^ (i.val + 1) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hP]
    linarith [mul_comm ‖U i j'‖ ‖∏ t : Fin (i.val + 1), d (Fin.castLE i.isLt t)‖]
  have h3 : m ^ (i.val + 1) ≤ (1 + δ⁻¹) * m ^ p := pow_le_of_lb hm hδ hδm i.isLt
  have h4 : ((i.val + 1).factorial : ℝ) / ‖∏ t : Fin (i.val + 1), d (Fin.castLE i.isLt t)‖ ≤
      ∑ i : Fin p, ((i.val + 1).factorial : ℝ) / ‖∏ t : Fin (i.val + 1), d (Fin.castLE i.isLt t)‖ :=
    Finset.single_le_sum (f := fun i : Fin p =>
      ((i.val + 1).factorial : ℝ) / ‖∏ t : Fin (i.val + 1), d (Fin.castLE i.isLt t)‖)
      (fun _ _ => by positivity) (Finset.mem_univ i)
  calc ‖U i j'‖ ≤ _ := h2
    _ ≤ _ := mul_le_mul h4 h3 (by positivity) (le_trans (by positivity) h4)
end Formalism.FourierDecayAlt.P.Ux5
