-- Prove2me | solution 1 for Formalism.SL.P.frame_gram_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:47:37.776526+00:00
-- url     : https://prove2.me/submissions/e18837ce-cf60-4987-92a4-fd02bb1a5ce8

import Mathlib
import Definitions.Def_Formalism_SobolevGaussianKernels_StatementFU
import Definitions.Def_Formalism_SobolevGaussianKernels_GaussianKernelBounds_NeighbourhoodHilbertSchmidtHolds
import Theorems.Thm_Formalism_SL_P_fu_sum_comp
import Theorems.Thm_Formalism_SL_P_fu_comp_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.SL Formalism.SL.P
open Finset Module LinearMap Formalism.CorankShareLayerCake.FR Formalism.SL.FU
open scoped InnerProductSpace ComplexConjugate
namespace Formalism.SL.P
theorem _root_.solution : FrameGram := by
  intro ι _ V _ _ _ H _ _ _ B c
  have kc : ∀ i j, trace ℂ H (B i ∘ₗ adjoint (B i) ∘ₗ B j ∘ₗ adjoint (B j)) =
      trace ℂ (V j) (adjoint (adjoint (B i) ∘ₗ B j) ∘ₗ adjoint (B i) ∘ₗ B j) := by
    intro i j
    rw [LinearMap.adjoint_comp, LinearMap.adjoint_adjoint]
    have h := LinearMap.trace_comp_comm' (adjoint (B j)) (B i ∘ₗ adjoint (B i) ∘ₗ B j)
    simp only [LinearMap.comp_assoc] at h ⊢
    exact h
  refine ⟨?_, ?_⟩
  · rw [frQ.eq_1]
    simp only [fu_sum_comp, fu_comp_sum, LinearMap.smul_comp, LinearMap.comp_smul,
      LinearMap.comp_assoc, map_sum, map_smul, smul_eq_mul, kc, Finset.mul_sum, Complex.re_sum,
      Complex.re_ofReal_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hs2.eq_1]
    ring
  · rw [frQ.eq_1]
    simp only [map_sum, map_smul, smul_eq_mul, Complex.re_sum, Complex.re_ofReal_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.trace_comp_comm']
end Formalism.SL.P
