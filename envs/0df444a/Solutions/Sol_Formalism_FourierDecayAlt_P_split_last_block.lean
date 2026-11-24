-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.split_last_block
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:04:16.3728+00:00
-- url     : https://prove2.me/submissions/7fe4f03f-a2fb-43a0-93d2-342f8ee36059

import Definitions.Def_Formalism_HermitianCurvature_StatementTA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagonalTopBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_TA1_sqrt_form_sum_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_TA1_ls_mem_Icc
import Theorems.Thm_Formalism_FourierDecayAlt_P_TA1_sum_PT_ls

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.TA Finset Filter Topology TA1
open scoped InnerProductSpace ComplexConjugate
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.TA.SplitLast := by
  intro E _ _ H _ _ W D Sg Φ w i _ hi hK
  let U : ℕ → Pt E → H := fun s p => if ls p = s then Φ w p else 0
  have h1 : Slev D Sg Φ w i =
      (form (PT Sg i) (D.K i) (∑ s ∈ Icc 1 i, U s) (∑ s ∈ Icc 1 i, U s)).re := by
    have hU : ∀ p ∈ PT Sg i, (∑ s ∈ Icc 1 i, U s) p = Φ w p := by
      intro p hp
      rw [Finset.sum_apply]
      simp only [U]
      rw [sum_ite_eq, if_pos (ls_mem_Icc Sg i hi p hp)]
    unfold Slev gram form
    congr 1
    refine sum_congr rfl fun p hp => sum_congr rfl fun p' hp' => ?_
    rw [hU p hp, hU p' hp']
  have h2 : ∀ s ∈ Icc 1 i, Ssplit D Sg Φ w i s = (form (PT Sg i) (D.K i) (U s) (U s)).re := by
    intro s hs
    obtain ⟨hs1, hsi⟩ := mem_Icc.1 hs
    have e : form (PT Sg i) (D.K i) (U s) (U s) =
        ∑ p ∈ PT Sg i, if ls p = s then
          (∑ p' ∈ PT Sg i, if ls p' = s then D.K i p p' * ⟪Φ w p, Φ w p'⟫_ℂ else 0) else 0 := by
      unfold form
      refine sum_congr rfl fun p _ => ?_
      by_cases hp : ls p = s
      · rw [if_pos hp]
        refine sum_congr rfl fun p' _ => ?_
        by_cases hp' : ls p' = s
        · simp only [U, if_pos hp, if_pos hp']
        · simp only [U, if_neg hp', inner_zero_right, mul_zero]
      · rw [if_neg hp]
        refine sum_eq_zero fun p' _ => ?_
        simp only [U, if_neg hp, inner_zero_left, mul_zero]
    rw [e, sum_PT_ls Sg i s hs1 hsi]
    unfold Ssplit Nst offK
    congr 1
    refine sum_congr rfl fun t _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun h _ => ?_
    rw [sum_PT_ls Sg i s hs1 hsi]
  rw [h1]
  refine (sqrt_form_sum_le (PT Sg i) (D.K i) hK (Icc 1 i) U).trans (le_of_eq ?_)
  exact sum_congr rfl fun s hs => by rw [h2 s hs]
end Formalism.FourierDecayAlt.P
