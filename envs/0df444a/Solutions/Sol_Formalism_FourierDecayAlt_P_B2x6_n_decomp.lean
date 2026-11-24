-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x6.n_decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:28:29.830296+00:00
-- url     : https://prove2.me/submissions/7fd3d5fa-0fba-45fb-be1c-352c70bf84e3

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_iF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lv_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lv_ne_iF
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lv_inj
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_vext
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_herm3
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_herm_zero_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_uh_of_herm
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_mat_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_hermitian_form_base_vector_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lev_mulVec_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lev_mulVec_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lev_mulVec_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_heis_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_heis_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_heis_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_herm_self_real
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_ent
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_mulVec3
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_herm_zero_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_mat_ext
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_nset_iff
import Theorems.Thm_Formalism_QuantumDeterminants_ggHerm_unitary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_first_eq_one
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_last_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_first_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_last
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_F
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_L
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_res

set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x6
theorem _root_.solution {g : Mat k (1 + r')} (hg : g ∈ Nset k (1 + r')) :
    ∃ x : HPar k r', blk g ∈ Nset k r' ∧ g = heis0 k r' x * ιLev k 1 r' (blk g) := by
  rw [WeylGroupFacts.nset_iff] at hg
  obtain ⟨hU, hc⟩ := hg
  have inv := ggHerm_unitary (Hpk k (1 + r')) g hU

  have cF : ∀ p, g p (iF k r') = if p = iF k r' then 1 else 0 := by
    intro p
    exact hc p (iF k r') (by rw [iF_val]; omega) (by rw [iF_val]; omega)
  have ge : g *ᵥ e0 k r' = e0 k r' := by
    funext p
    have := ent g p (iF k r')
    rw [cF] at this
    show (g *ᵥ bvec (iF k r')) p = bvec (iF k r') p
    rw [← this, bvec, Pi.single_apply]

  have gL : ∀ u, (g *ᵥ u) (iL k r') = u (iL k r') := by
    intro u
    rw [← hermitian_form_base_vector_right (g *ᵥ u), ← hermitian_form_base_vector_right u, ← inv u (e0 k r'), ge]
  set y : Fin (2 * r' + k + 1) → ℂ := fun i => g (lv k r' i) (iL k r') with hy
  set β : ℂ := g (iF k r') (iL k r') with hβ
  set aa : (Fin (2 * r' + k + 1) → ℂ) → ℂ := fun z => ∑ j, g (iF k r') (lv k r' j) * z j with haa
  have gF : ∀ u, (g *ᵥ u) (iF k r') = u (iF k r') + aa (res u) + β * u (iL k r') := by
    intro u
    rw [mulVec3, cF, if_pos rfl, one_mul]
  have gm : ∀ u, res (g *ᵥ u) = blk g *ᵥ res u + u (iL k r') • y := by
    intro u
    funext i
    simp only [res]
    rw [mulVec3, cF, if_neg (lv_ne_iF i)]
    simp [blk, mulVec, dotProduct, res, hy, mul_comm]

  have r1 : ∀ z, aa z = - herm (Hpk k r') (blk g *ᵥ z) y := by
    intro z
    have h := inv (liftVec k 1 r' z) (es0 k r')
    rw [herm3, herm3 (liftVec k 1 r' z), gF, gF, gL, gL, gm, gm] at h
    simp [herm_zero_right] at h
    linear_combination h
  have r2 : β + star β = - herm (Hpk k r') y y := by
    have h := inv (es0 k r') (es0 k r')
    rw [herm3, herm3 (es0 k r'), gF, gL, gm] at h
    simp [herm_zero_right, haa] at h
    rw [Complex.star_def]
    linear_combination h
  have r3 : β = hb k r' y β.im := by
    rw [herm_self_real y] at r2
    have := congrArg Complex.re r2
    simp at this
    apply Complex.ext
    · simp [hb]; linarith
    · simp [hb]
  refine ⟨(y, β.im), ?_, ?_⟩
  · rw [WeylGroupFacts.nset_iff]
    constructor
    · apply uh_of_herm
      intro z z'
      have h := inv (liftVec k 1 r' z) (liftVec k 1 r' z')
      rw [herm3, herm3 (liftVec k 1 r' z), gL, gL, gm, gm] at h
      simpa using h
    · intro i j hj hi
      show g (lv k r' i) (lv k r' j) = _
      rw [hc _ _ (by rw [lv_val]; omega) (by rw [lv_val, lv_val]; omega)]
      simp only [lv_inj]
  · apply mat_ext
    intro u
    rw [← mulVec_mulVec]
    apply vext
    · rw [heis_F, lev_mulVec_F, lev_mulVec_L, lev_mulVec_res, gF, r1]
      simp only
      rw [← r3]
      ring
    · rw [heis_res, lev_mulVec_res, lev_mulVec_L, gm]
    · rw [heis_L, lev_mulVec_L, gL]
end Formalism.FourierDecayAlt.P.B2x6
