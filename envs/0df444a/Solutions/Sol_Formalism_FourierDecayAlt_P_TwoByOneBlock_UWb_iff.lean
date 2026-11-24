-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoByOneBlock.UWb_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:35:17.921566+00:00
-- url     : https://prove2.me/submissions/707ce3b1-513b-4857-88f5-8b8dc71c799b

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_emb_out_col
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_emb_out_row
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_mid_exists
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_emb_wI
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_sig_out
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_Hpk_out_mid
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_emb_form
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_emb_mem_UWb
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_Hpk_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_emb_form
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_emb_out_col
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_emb_out_row
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_In_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_Wb_emb_out_col
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_Wb_emb_out_row
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_Wb_emb_wI
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_eq
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_sig_sig


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TwoByOneBlock
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.TwoByOneBlock
theorem _root_.solution (g : Mat k r) : g ∈ UWb k r ↔ ∃ μ ∈ UH (Hb k), g = embWb k r μ := by
  constructor
  · rintro ⟨hg, hfix⟩
    have hcol : ∀ i j, ¬ mid k r j → g i j = if i = j then 1 else 0 := by
      intro i j hj
      have hjl := j.isLt
      have key : g *ᵥ bvec j = bvec j := by
        by_cases h1 : j.val < r
        · have e : eI k r ⟨j.val, h1⟩ = j := Fin.ext rfl
          have := (hfix ⟨j.val, h1⟩).1
          rwa [e] at this
        · have h2 : r + k < j.val := by
            by_contra h2
            exact hj ⟨by omega, by omega⟩
          have e : esI k r ⟨2 * r + k - j.val, by omega⟩ = j := Fin.ext (by simp only [esI]; omega)
          have := (hfix ⟨2 * r + k - j.val, by omega⟩).2
          rwa [e] at this
      have := congrFun key i
      unfold bvec at this
      rw [Matrix.mulVec_single_one, Pi.single_apply] at this
      exact this
    have hrow : ∀ i j, ¬ mid k r i → mid k r j → g i j = 0 := by
      intro i j hi hj
      have hp := sig_out hi
      have h : (gᴴ * Hpk k r * g) (GBasic.sig k r i) j = Hpk k r (GBasic.sig k r i) j := by
        have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
        rw [hg']
      rw [Hpk_out_mid hp hj, Matrix.mul_apply] at h
      have h1 : ∀ b, (gᴴ * Hpk k r) (GBasic.sig k r i) b = Hpk k r (GBasic.sig k r i) b := by
        intro b
        rw [Matrix.mul_apply, Finset.sum_eq_single (GBasic.sig k r i)]
        · rw [Matrix.conjTranspose_apply, hcol _ _ hp, if_pos rfl, star_one, one_mul]
        · intro q _ hq
          rw [Matrix.conjTranspose_apply, hcol _ _ hp, if_neg hq, star_zero, zero_mul]
        · intro h; exact absurd (Finset.mem_univ _) h
      simp only [h1] at h
      rw [Finset.sum_eq_single i] at h
      · rw [GBasic.Hpk_eq, GBasic.sig_sig, if_pos rfl] at h
        have hs : GBasic.sgn k r (GBasic.sig k r i) ≠ 0 := by
          unfold GBasic.sgn
          split_ifs <;> simp
        exact (mul_eq_zero.1 h).resolve_left hs
      · intro q _ hq
        rw [GBasic.Hpk_eq, GBasic.sig_sig, if_neg hq, zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hge : g = embWb k r (Matrix.of fun a b => g (wI k r a) (wI k r b)) := by
      ext i j
      by_cases hj : mid k r j
      · by_cases hi : mid k r i
        · obtain ⟨x, rfl⟩ := mid_exists hi
          obtain ⟨y, rfl⟩ := mid_exists hj
          rw [emb_wI, Matrix.of_apply]
        · rw [hrow i j hi hj, emb_out_row _ _ _ hi, if_neg (show ¬ (i = j) from fun h => hi (h ▸ hj))]
      · rw [hcol i j hj, emb_out_col _ _ _ hj]
    refine ⟨_, ?_, hge⟩
    rw [← emb_form (r := r), ← hge]
    exact hg
  · rintro ⟨μ, hμ, rfl⟩
    exact emb_mem_UWb hμ
end Formalism.FourierDecayAlt.P.TwoByOneBlock
