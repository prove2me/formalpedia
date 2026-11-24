-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoByOneBlock.emb_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:54:03.960421+00:00
-- url     : https://prove2.me/submissions/a7202e0d-28ff-4e74-af42-25903751236e

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_mid_wI
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_mid_exists
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_mul_emb_out
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_mul_emb_mid
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_emb_mul_out
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_emb_mul_mid
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_Hpk_wI
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_Hpk_mid_out
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_Hpk_out_mid
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_emb_conjTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_emb_form_mid

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
theorem _root_.solution (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    embWb k r μ ∈ GV k r ↔ μ ∈ UH (Hb k) := by
  constructor
  · intro h
    have h' : (embWb k r μ)ᴴ * Hpk k r * embWb k r μ = Hpk k r := h
    show μᴴ * Hb k * μ = Hb k
    ext a b
    rw [← emb_form_mid (r := r), h', Hpk_wI]
  · intro h
    have h' : μᴴ * Hb k * μ = Hb k := h
    show (embWb k r μ)ᴴ * Hpk k r * embWb k r μ = Hpk k r
    ext i j
    by_cases hi : mid k r i
    · by_cases hj : mid k r j
      · obtain ⟨x, rfl⟩ := mid_exists hi
        obtain ⟨y, rfl⟩ := mid_exists hj
        rw [emb_form_mid, h', Hpk_wI]
      · obtain ⟨x, rfl⟩ := mid_exists hi
        rw [mul_emb_out _ _ _ _ hj, emb_conjTranspose, emb_mul_mid, Hpk_mid_out hi hj]
        apply Finset.sum_eq_zero
        intro c _
        rw [Hpk_mid_out (mid_wI c) hj, mul_zero]
    · by_cases hj : mid k r j
      · obtain ⟨y, rfl⟩ := mid_exists hj
        rw [mul_emb_mid, Hpk_out_mid hi hj]
        apply Finset.sum_eq_zero
        intro c _
        rw [emb_conjTranspose, emb_mul_out _ _ _ _ hi, Hpk_out_mid hi (mid_wI c), zero_mul]
      · rw [mul_emb_out _ _ _ _ hj, emb_conjTranspose, emb_mul_out _ _ _ _ hi]
end Formalism.FourierDecayAlt.P.TwoByOneBlock
