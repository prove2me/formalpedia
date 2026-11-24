-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoByOneBlock.map_Sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:56:21.642679+00:00
-- url     : https://prove2.me/submissions/40f557ec-6bb8-41f5-93b6-e59d7918f533

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_Sq_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_Sq_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_ext_Iic
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_Vb_ne_top
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_vol_Sq_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_dens_Iic

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
open Set
open scoped Pointwise
namespace Formalism.FourierDecayAlt.P.TwoByOneBlock
theorem _root_.solution (n : ℕ) :
    Measure.map (Sq (n + 1)) volume = ((n + 1 : ℕ) * Vb (n + 1) : ℝ≥0∞) • dens n := by
  have hF : ∀ b, Measure.map (Sq (n + 1)) volume (Iic b) = ENNReal.ofReal ((max b 0) ^ (n + 1)) * Vb (n + 1) := by
    intro b
    rw [Measure.map_apply (Sq_cont _).measurable measurableSet_Iic]
    rcases le_total 0 b with hb | hb
    · rw [max_eq_left hb]; exact vol_Sq_le n hb
    · rcases hb.eq_or_lt with rfl | hb'
      · rw [max_self]; exact vol_Sq_le n le_rfl
      · rw [max_eq_right hb]
        have : Sq (n + 1) ⁻¹' Iic b = ∅ := by
          ext x; simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false, not_le]
          exact hb'.trans_le (Sq_nonneg x)
        rw [this]; simp
  refine ext_Iic _ _ (fun b => ?_) (fun b => ?_)
  · rw [hF, Measure.smul_apply, dens_Iic, smul_eq_mul]
    have h0 : (0 : ℝ) ≤ max b 0 := le_max_right _ _
    rw [ENNReal.ofReal_div_of_pos (by positivity)]
    have : ENNReal.ofReal ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ≥0∞) := by
      rw [← Nat.cast_succ, ENNReal.ofReal_natCast]
    rw [this]
    have hne : ((n + 1 : ℕ) : ℝ≥0∞) ≠ 0 := by simp
    have hnt : ((n + 1 : ℕ) : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
    rw [mul_comm (((n + 1 : ℕ) : ℝ≥0∞)) _, mul_assoc, ENNReal.mul_div_cancel hne hnt, mul_comm]
  · rw [hF]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Vb_ne_top _)
end Formalism.FourierDecayAlt.P.TwoByOneBlock
