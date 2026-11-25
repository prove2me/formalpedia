-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HLsc.schur
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:47:56.167956+00:00
-- url     : https://prove2.me/submissions/8e4a46f7-5556-440f-9617-9e30a4c488b4

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Herglotz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HerglotzLowerSemicontinuous
import Theorems.Thm_Formalism_FourierDecayAlt_P_HLsc_sum_sub_le_tsum
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_HLsc_sum_sub_le_tsum__f9098793113c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HLsc
open Real Filter Topology Finset MeasureTheory Formalism.FourierDecayAlt.P.Herglotz
variable {d : ℕ}
namespace Formalism.FourierDecayAlt.P.HLsc
theorem _root_.solution {κ : (Fin d → ℤ) → ℝ} (hκ0 : ∀ σ, 0 ≤ κ σ) (hκ : Summable κ)
    (B : Finset (Fin d → ℤ)) (a : (Fin d → ℤ) → ℝ) :
    ∑ σ ∈ B, ∑ σ' ∈ B, κ (σ - σ') * a σ * a σ' ≤ (∑' τ, κ τ) * ∑ σ ∈ B, a σ ^ 2 := by
  have h1 : ∑ σ ∈ B, ∑ σ' ∈ B, κ (σ - σ') * a σ * a σ' ≤
      ∑ σ ∈ B, ∑ σ' ∈ B, (κ (σ - σ') * (a σ ^ 2 / 2) + κ (σ - σ') * (a σ' ^ 2 / 2)) := by
    refine Finset.sum_le_sum (fun σ _ => Finset.sum_le_sum (fun σ' _ => ?_))
    have := hκ0 (σ - σ')
    nlinarith [mul_nonneg this (sq_nonneg (a σ - a σ'))]
  refine h1.trans ?_
  simp_rw [Finset.sum_add_distrib]
  have h2 : ∑ σ ∈ B, ∑ σ' ∈ B, κ (σ - σ') * (a σ ^ 2 / 2) ≤
      ∑ σ ∈ B, (∑' τ, κ τ) * (a σ ^ 2 / 2) := by
    refine Finset.sum_le_sum (fun σ _ => ?_)
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (sum_sub_le_tsum hκ0 hκ B σ) (by positivity)
  have h3 : ∑ σ ∈ B, ∑ σ' ∈ B, κ (σ - σ') * (a σ' ^ 2 / 2) ≤
      ∑ σ' ∈ B, (∑' τ, κ τ) * (a σ' ^ 2 / 2) := by
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum (fun σ' _ => ?_)
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (sum_sub_le_tsum' hκ0 hκ B σ') (by positivity)
  refine (add_le_add h2 h3).trans (le_of_eq ?_)
  rw [← Finset.mul_sum, ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  ring
end Formalism.FourierDecayAlt.P.HLsc
