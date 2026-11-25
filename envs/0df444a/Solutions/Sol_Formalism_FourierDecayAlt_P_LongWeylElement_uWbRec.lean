-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LongWeylElement.uWbRec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:48:00.565131+00:00
-- url     : https://prove2.me/submissions/c1510ee8-7a0f-43c7-83fb-2c15b801e88a

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_mid_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_lev_mm
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_lev_mn
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_lev_n
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_not_mid_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_lev_col_n
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_lev_UH
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_fix_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_lev_col_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_eI_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_esI_succ
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_LongWeylElement_fin_cases__0856e4f673a2
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_Hpk_Z
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_Hpk_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_row_of_col
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_lev_mm
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_lev_mn
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_lev_n
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_mid_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lev_mm
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lev_n
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
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
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LongWeylElement
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.LongWeylElement
theorem _root_.solution : Formalism.FourierDecayAlt.B2.UWbRec := by
  intro k r'
  ext g
  constructor
  · rintro ⟨hG, hfix⟩
    have cZ : ∀ p, g p (iZ k r') = if p = iZ k r' then 1 else 0 := (fix_iff g _).1 (hfix (a0 r')).1
    have cL : ∀ p, g p (iL k r') = if p = iL k r' then 1 else 0 := (fix_iff g _).1 (hfix (a0 r')).2
    have hGe : gᴴ * Hpk k (1 + r') * g = Hpk k (1 + r') := hG
    have rL : ∀ q, g (iL k r') q = if q = iL k r' then 1 else 0 := by
      intro q
      have h1 := row_of_col g (Hpk k (1 + r')) (iZ k r') q cZ
      rw [hGe, Matrix.mul_apply] at h1
      first
        | (simp only [Hpk_Z, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ,
            ite_true] at h1
           exact h1.symm)
        | (simp [Hpk_Z] at h1
           exact h1.symm)
    have rZ : ∀ q, g (iZ k r') q = if q = iZ k r' then 1 else 0 := by
      intro q
      have h1 := row_of_col g (Hpk k (1 + r')) (iL k r') q cL
      rw [hGe, Matrix.mul_apply] at h1
      first
        | (simp only [Hpk_L, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ,
            ite_true] at h1
           exact h1.symm)
        | (simp [Hpk_L] at h1
           exact h1.symm)
    have hg : g = ιLev k 1 r' (Matrix.of (blk k r' g)) := by
      ext p q
      by_cases hp : mid k r' p
      · by_cases hq : mid k r' q
        · obtain ⟨s, rfl⟩ := (mid_iff k r' p).1 hp
          obtain ⟨t, rfl⟩ := (mid_iff k r' q).1 hq
          rw [lev_mm]
          rfl
        · rw [lev_mn k r' _ p q hp hq]
          rcases (not_mid_iff q).1 hq with rfl | rfl
          · rw [cZ, if_neg]
            rintro rfl
            exact hq hp
          · rw [cL, if_neg]
            rintro rfl
            exact hq hp
      · rw [lev_n k r' _ p q hp]
        rcases (not_mid_iff p).1 hp with rfl | rfl
        · rw [rZ]
          exact if_congr eq_comm rfl rfl
        · rw [rL]
          exact if_congr eq_comm rfl rfl
    refine ⟨Matrix.of (blk k r' g), ⟨?_, ?_⟩, hg.symm⟩
    · rw [← lev_UH, ← hg]
      exact hG
    · intro a
      constructor
      · have := (hfix (Fin.natAdd 1 a)).1
        rw [eI_succ, fix_iff, hg, lev_col_iff] at this
        exact (fix_iff _ _).2 this
      · have := (hfix (Fin.natAdd 1 a)).2
        rw [esI_succ, fix_iff, hg, lev_col_iff] at this
        exact (fix_iff _ _).2 this
  · rintro ⟨g', ⟨hG', hfix'⟩, rfl⟩
    refine ⟨(lev_UH g').2 hG', fun a => ?_⟩
    rcases fin_cases' a with rfl | ⟨a', rfl⟩
    · constructor
      · rw [fix_iff]
        intro p
        exact lev_col_n g' p _ (by rw [not_mid_iff]; exact Or.inl rfl)
      · rw [fix_iff]
        intro p
        exact lev_col_n g' p _ (by rw [not_mid_iff]; exact Or.inr rfl)
    · constructor
      · rw [eI_succ, fix_iff, lev_col_iff]
        exact (fix_iff g' _).1 (hfix' a').1
      · rw [esI_succ, fix_iff, lev_col_iff]
        exact (fix_iff g' _).1 (hfix' a').2
end Formalism.FourierDecayAlt.P.LongWeylElement
