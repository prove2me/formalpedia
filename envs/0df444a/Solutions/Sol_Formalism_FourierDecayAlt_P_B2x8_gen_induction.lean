-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.gen_induction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:11:59.308396+00:00
-- url     : https://prove2.me/submissions/524041c1-cc61-4672-869e-23ee2d0c39a7

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_three_block_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_three_block_eta
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_dual_base_vector_eq_single
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_lift_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_al_herm_zero_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_al_mul_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_al_unit
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_al_cL_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_heis_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_cmHalfIntegralGenerator_mem_algebraicClosure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_al_heis_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_heisenberg_dual_base_vector
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_long_weyl_element_base_vector
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_al_oneStep_exists
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_al_phi

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
theorem _root_.solution (P : Mat k (1 + r') → Prop) (hmul : ∀ a b, P a → P b → P (a * b))
    (hcancel : ∀ a b, P (a * b) → P b → P a)
    (hH : ∀ x, P (heis0 k r' x)) (hw : ∀ c, c ≠ 0 → P (w0 k r' c)) (hl : ∀ g₁ ∈ GV k r', P (ιLev k 1 r' g₁)) :
    ∀ g ∈ GV k (1 + r'), P g := by
  have big : ∀ g ∈ GV k (1 + r'), herm (Hpk k (1 + r')) (g *ᵥ e0 k r') (e0 k r') ≠ 0 → P g := by
    intro g hg hc
    obtain ⟨x, g₁, x', hg₁, he⟩ := al_oneStep_exists hg hc
    rw [he]
    unfold oneStep
    rw [al_heis_inv]
    exact hmul _ _ (hmul _ _ (hmul _ _ (hH _) (hw _ hc)) (hl _ hg₁)) (hH _)
  intro g hg
  by_cases hc : herm (Hpk k (1 + r')) (g *ᵥ e0 k r') (e0 k r') = 0
  · have hex : ∃ x : HPar k r', herm (Hpk k (1 + r')) (g *ᵥ mk3 k r' (hb k r' x.1 x.2) x.1 1) (e0 k r') ≠ 0 := by
      by_contra hno
      push Not at hno
      have h1 : ∀ y, herm (Hpk k (1 + r')) (g *ᵥ mk3 k r' 0 y 0) (e0 k r') +
          herm (Hpk k (1 + r')) (g *ᵥ es0 k r') (e0 k r') = 0 := by
        intro y
        have := hno (y, 0)
        rw [al_phi, hc] at this
        simpa using this
      have h2 : herm (Hpk k (1 + r')) (g *ᵥ es0 k r') (e0 k r') = 0 := by
        have := h1 0
        have hz : mk3 k r' 0 0 0 = 0 := by rw [← lift_eq]; ext i; simp [liftVec]
        rw [hz, Matrix.mulVec_zero, al_herm_zero_left, zero_add] at this
        exact this
      have h3 : ∀ u, herm (Hpk k (1 + r')) (g *ᵥ u) (e0 k r') = 0 := by
        intro u
        rw [← three_block_eta u, al_phi, hc, h2]
        have := h1 (mid u)
        rw [h2, add_zero] at this
        rw [this]; simp
      have h4 := h3 (g⁻¹ *ᵥ es0 k r')
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (al_unit hg), Matrix.one_mulVec, al_cL_eq, dual_base_vector_eq_single, three_block_last] at h4
      exact one_ne_zero h4
    obtain ⟨x, hx⟩ := hex
    have hPh : P (heis0 k r' x * w0 k r' 1) := hmul _ _ (hH x) (hw 1 one_ne_zero)
    apply hcancel g (heis0 k r' x * w0 k r' 1) _ hPh
    apply big _ (al_mul_mem hg (al_mul_mem (heis_mem x) (cmHalfIntegralGenerator_mem_algebraicClosure 1 one_ne_zero)))
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, long_weyl_element_base_vector, ← dual_base_vector_eq_single, heisenberg_dual_base_vector]
    exact hx
  · exact big g hg hc
end Formalism.FourierDecayAlt.P.B2x8
