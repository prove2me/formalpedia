-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.al_oneStep_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:28:17.921877+00:00
-- url     : https://prove2.me/submissions/4c9bb14d-0f83-4cff-83ed-6be8817d7a5e

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_herm_add_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_three_block_injective
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_herm_nondeg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_hb_im
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_levi_three_block
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_heisenberg_three_block
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_al_herm_neg_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_al_mul_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_al_unit
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_al_inv_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_heis_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_cmHalfIntegralGenerator_mem_algebraicClosure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_al_mat_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_heisenberg_dual_base_vector
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_one_parameter_element_base_vector

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x8
theorem _root_.solution {x x' z z' : HPar k r'} {c : ℂ} (hc : c ≠ 0) {g₁ h₁ : Mat k r'}
    (h : oneStep k r' x c g₁ x' = oneStep k r' z c h₁ z') : x = z ∧ g₁ = h₁ ∧ x' = z' := by
  have h0 := congrArg (fun A => A *ᵥ e0 k r') h
  simp only [one_parameter_element_base_vector] at h0
  obtain ⟨ha, hy, -⟩ := three_block_injective h0
  have hx1 : x.1 = z.1 := by
    have := smul_right_injective _ hc hy
    exact neg_injective this
  have hx2 : x.2 = z.2 := by
    have := congrArg Complex.im (mul_left_cancel₀ hc ha)
    rw [hb_im, hb_im] at this
    exact neg_injective this
  have hxz : x = z := Prod.ext hx1 hx2
  subst hxz
  have hA : IsUnit ((heis0 k r' x)⁻¹ * w0 k r' c).det := al_unit (al_mul_mem (al_inv_mem (heis_mem x)) (cmHalfIntegralGenerator_mem_algebraicClosure c hc))
  have h' : ιLev k 1 r' g₁ * heis0 k r' x' = ιLev k 1 r' h₁ * heis0 k r' z' := by
    unfold oneStep at h
    rw [Matrix.mul_assoc ((heis0 k r' x)⁻¹ * w0 k r' c), Matrix.mul_assoc ((heis0 k r' x)⁻¹ * w0 k r' c)] at h
    have := congrArg (fun B => ((heis0 k r' x)⁻¹ * w0 k r' c)⁻¹ * B) h
    simpa only [Matrix.nonsing_inv_mul_cancel_left _ _ hA] using this
  have hm : ∀ y, mk3 k r' (- herm (Hpk k r') y x'.1) (g₁ *ᵥ y) 0 = mk3 k r' (- herm (Hpk k r') y z'.1) (h₁ *ᵥ y) 0 := by
    intro y
    have := congrArg (fun A => A *ᵥ mk3 k r' 0 y 0) h'
    simp only [← Matrix.mulVec_mulVec, heisenberg_three_block, levi_three_block] at this
    simpa using this
  have hg : g₁ = h₁ := al_mat_ext fun y => (three_block_injective (hm y)).2.1
  have hy' : x'.1 = z'.1 := by
    have : x'.1 + -z'.1 = 0 := by
      apply herm_nondeg
      intro y
      rw [herm_add_right, al_herm_neg_right]
      have := (three_block_injective (hm y)).1
      linear_combination -this
    exact add_neg_eq_zero.1 this
  have hs' : x'.2 = z'.2 := by
    have := congrArg (fun A => A *ᵥ es0 k r') h'
    simp only [← Matrix.mulVec_mulVec, heisenberg_dual_base_vector, levi_three_block] at this
    have := congrArg Complex.im (three_block_injective this).1
    rwa [hb_im, hb_im] at this
  exact ⟨rfl, hg, Prod.ext hy' hs'⟩
end Formalism.FourierDecayAlt.P.B2x8
