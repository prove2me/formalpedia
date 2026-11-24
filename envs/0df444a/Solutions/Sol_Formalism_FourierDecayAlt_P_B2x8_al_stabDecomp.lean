-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.al_stabDecomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:28:23.88846+00:00
-- url     : https://prove2.me/submissions/051e722c-d357-4ccb-9ae8-8cfd99c0cfb5

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_herm_UH
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_three_block_first
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_three_block_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_three_block_eta
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_dual_base_vector_eq_single
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_hermitian_three_block
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_eq_hb
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_al_inv_mulVec
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_al_mul_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_al_unit
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_al_inv_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_al_cL_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_al_cF_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_heis_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_lev_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_heisenberg_fixes_isotropic_vector
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_heisenberg_dual_base_vector
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_levi_fixes_isotropic_vector
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_al_fix

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
theorem _root_.solution : StabDecomp := by
  intro k r'
  ext g
  constructor
  · rintro ⟨hg, he⟩
    have hb1 : cL (g *ᵥ es0 k r') = 1 := by
      rw [← al_cL_eq]
      conv_lhs => rw [← he]
      rw [herm_UH _ hg, al_cL_eq, dual_base_vector_eq_single, three_block_last]
    have hq : herm (Hpk k (1 + r')) (g *ᵥ es0 k r') (g *ᵥ es0 k r') = 0 := by
      rw [herm_UH _ hg, al_cF_eq, dual_base_vector_eq_single, three_block_first]
    rw [← three_block_eta (g *ᵥ es0 k r'), hermitian_three_block, hb1] at hq
    have ha : cF (g *ᵥ es0 k r') = hb k r' (mid (g *ᵥ es0 k r')) (cF (g *ᵥ es0 k r')).im := by
      apply eq_hb
      simp only [map_one, mul_one, one_mul] at hq
      linear_combination hq
    set x : HPar k r' := (mid (g *ᵥ es0 k r'), (cF (g *ᵥ es0 k r')).im) with hx
    have hn := heis_mem x
    have hnes : heis0 k r' x *ᵥ es0 k r' = g *ᵥ es0 k r' := by
      rw [heisenberg_dual_base_vector, ← three_block_eta (g *ᵥ es0 k r'), hb1]
      conv_rhs => rw [ha]
    obtain ⟨g₁, hg₁, hgg⟩ := al_fix (h := (heis0 k r' x)⁻¹ * g) (al_mul_mem (al_inv_mem hn) hg)
      (by rw [← Matrix.mulVec_mulVec, he]; exact al_inv_mulVec (al_unit hn) (heisenberg_fixes_isotropic_vector x))
      (by rw [← Matrix.mulVec_mulVec]; exact al_inv_mulVec (al_unit hn) hnes)
    refine ⟨heis0 k r' x, ⟨x, rfl⟩, ιLev k 1 r' g₁, ⟨g₁, hg₁, rfl⟩, ?_⟩
    rw [← hgg, Matrix.mul_nonsing_inv_cancel_left _ _ (al_unit hn)]
  · rintro ⟨n, ⟨x, rfl⟩, l, ⟨g₁, hg₁, rfl⟩, rfl⟩
    refine ⟨al_mul_mem (heis_mem x) (lev_mem g₁ hg₁), ?_⟩
    rw [← Matrix.mulVec_mulVec, levi_fixes_isotropic_vector, heisenberg_fixes_isotropic_vector]
end Formalism.FourierDecayAlt.P.B2x8
