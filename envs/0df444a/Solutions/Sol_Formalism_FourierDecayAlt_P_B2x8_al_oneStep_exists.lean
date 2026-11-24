-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.al_oneStep_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:52:01.781802+00:00
-- url     : https://prove2.me/submissions/d088de80-6091-41a4-9c02-3b0c31cbd5ea

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_herm_smul_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_herm_smul_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_herm_UH
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_three_block_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_three_block_eta
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_e0_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_hermitian_three_block
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_eq_hb
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_heisenberg_three_block
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_al_herm_zero_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_al_inv_mulVec
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_al_mul_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_al_unit
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_al_inv_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_al_cL_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_heis_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_cmHalfIntegralGenerator_mem_algebraicClosure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_al_heis_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_al_lev_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_long_weyl_element_base_vector
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_al_stabDecomp

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
theorem _root_.solution {g : Mat k (1 + r')} (hg : g ∈ GV k (1 + r'))
    (hc : herm (Hpk k (1 + r')) (g *ᵥ e0 k r') (e0 k r') ≠ 0) :
    ∃ (x : HPar k r') (g₁ : Mat k r') (x' : HPar k r'), g₁ ∈ GV k r' ∧
      g = oneStep k r' x (herm (Hpk k (1 + r')) (g *ᵥ e0 k r') (e0 k r')) g₁ x' := by
  set c := herm (Hpk k (1 + r')) (g *ᵥ e0 k r') (e0 k r') with hcdef
  have hcL : cL (g *ᵥ e0 k r') = c := by rw [hcdef, al_cL_eq]
  have hc' : conj c ≠ 0 := (map_ne_zero _).2 hc
  have hq : herm (Hpk k (1 + r')) (g *ᵥ e0 k r') (g *ᵥ e0 k r') = 0 := by
    rw [herm_UH _ hg, al_cL_eq, e0_eq, three_block_last]
  rw [← three_block_eta (g *ᵥ e0 k r'), hermitian_three_block, hcL] at hq
  set α := cF (g *ᵥ e0 k r') with hα
  set y' := mid (g *ᵥ e0 k r') with hy'
  have hbb : α / c = hb k r' (c⁻¹ • y') (α / c).im := by
    apply eq_hb
    rw [herm_smul_left, herm_smul_right, map_div₀, map_inv₀]
    field_simp
    linear_combination hq
  set x₁ : HPar k r' := (c⁻¹ • y', (α / c).im) with hx₁
  have hn := heis_mem x₁
  have hw := cmHalfIntegralGenerator_mem_algebraicClosure (k := k) (r' := r') c hc
  have hu : heis0 k r' x₁ *ᵥ mk3 k r' 0 0 c = g *ᵥ e0 k r' := by
    rw [heisenberg_three_block, ← three_block_eta (g *ᵥ e0 k r'), hcL, ← hα, ← hy']
    have e1 : (0 : ℂ) - herm (Hpk k r') 0 x₁.1 + c * hb k r' x₁.1 x₁.2 = α := by
      rw [al_herm_zero_left, ← hbb]; field_simp; ring
    have e2 : (0 : Fin (2 * r' + k + 1) → ℂ) + c • x₁.1 = y' := by
      rw [zero_add, hx₁, smul_smul, mul_inv_cancel₀ hc, one_smul]
    rw [e1, e2]
  set p := (w0 k r' c)⁻¹ * ((heis0 k r' x₁)⁻¹ * g) with hp
  have hpm : p ∈ GV k (1 + r') := al_mul_mem (al_inv_mem hw) (al_mul_mem (al_inv_mem hn) hg)
  have hpe : p *ᵥ e0 k r' = e0 k r' := by
    rw [hp, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, al_inv_mulVec (al_unit hn) hu]
    exact al_inv_mulVec (al_unit hw) (long_weyl_element_base_vector c)
  have hpi : p⁻¹ ∈ P1set k r' := ⟨al_inv_mem hpm, al_inv_mulVec (al_unit hpm) hpe⟩
  rw [al_stabDecomp k r'] at hpi
  obtain ⟨n, ⟨x'', rfl⟩, l, ⟨g₁, hg₁, rfl⟩, hpp⟩ := hpi
  have hp2 : p = ιLev k 1 r' g₁⁻¹ * heis0 k r' (-x''.1, -x''.2) := by
    rw [← Matrix.nonsing_inv_nonsing_inv p (al_unit hpm), hpp, Matrix.mul_inv_rev, al_heis_inv, al_lev_inv (al_unit hg₁)]
  refine ⟨(-x₁.1, -x₁.2), g₁⁻¹, (-x''.1, -x''.2), al_inv_mem hg₁, ?_⟩
  unfold oneStep
  rw [al_heis_inv]
  simp only [neg_neg, Prod.mk.eta]
  rw [Matrix.mul_assoc (heis0 k r' x₁ * w0 k r' c), ← hp2, hp, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv_cancel_left _ _ (al_unit hw), Matrix.mul_nonsing_inv_cancel_left _ _ (al_unit hn)]
end Formalism.FourierDecayAlt.P.B2x8
