-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoByOneBlock.trans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:55:09.410889+00:00
-- url     : https://prove2.me/submissions/79ce5244-e50b-4f3e-b395-961cfb3f7f41

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_herm_add_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_herm_smul_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_herm_add_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_herm_smul_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_herm_symm
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_qrefl_mulVec
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_qrefl_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_exists_phase
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_UH_mul

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
namespace Formalism.FourierDecayAlt.P.TwoByOneBlock
theorem _root_.solution {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (hH : Hᴴ = H) (a b : Fin m → ℂ) (q : ℝ) (hq : q ≠ 0)
    (ha : herm H a a = q) (hb : herm H b b = q) :
    ∃ g ∈ UH H, g *ᵥ a = b ∧ ∀ x, herm H x a = 0 → herm H x b = 0 → g *ᵥ x = x := by
  obtain ⟨θ, hθ, t, ht, hqt⟩ := exists_phase (herm H a b) q
  have hqd : (q : ℝ) - t ≠ 0 := by
    intro h
    have : q * q ≤ 0 := by
      have : t = q := by linarith
      rw [this] at hqt; exact hqt
    have h2 : 0 < q * q := mul_self_pos.2 hq
    linarith
  have hqdC : (q : ℂ) - t ≠ 0 := by exact_mod_cast hqd
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  have hba : herm H b a = star (herm H a b) := herm_symm H hH a b
  have ht' : θ * star (herm H a b) = t := by
    have := congrArg star ht
    simpa using this
  set d : Fin m → ℂ := a + (-θ) • b with hd
  have had : herm H a d = (q : ℂ) - t := by
    rw [hd, herm_add_right, herm_smul_right, ha, star_neg]
    linear_combination -ht
  have hdd : herm H d d = 2 * ((q : ℂ) - t) := by
    rw [hd, herm_add_left, herm_smul_left, ← hd, had, hd, herm_add_right, herm_smul_right, hb, hba, star_neg]
    linear_combination (q : ℂ) * hθ - ht'
  have hR : qrefl H d (-1 / ((q : ℂ) - t)) ∈ UH H := by
    apply qrefl_mem H hH
    rw [hdd]
    have : star (-1 / ((q : ℂ) - t)) = -1 / ((q : ℂ) - t) := by simp
    rw [this]
    field_simp
    ring
  have hS : qrefl H b ((star θ - 1) / q) ∈ UH H := by
    apply qrefl_mem H hH
    rw [hb]
    have : star ((star θ - 1) / (q : ℂ)) = (θ - 1) / q := by simp
    rw [this]
    field_simp
    linear_combination hθ
  refine ⟨qrefl H b ((star θ - 1) / q) * qrefl H d (-1 / ((q : ℂ) - t)), UH_mul hS hR, ?_, ?_⟩
  · rw [← Matrix.mulVec_mulVec, qrefl_mulVec H d, had]
    have h1 : a + (-1 / ((q : ℂ) - t) * ((q : ℂ) - t)) • d = θ • b := by
      rw [div_mul_cancel₀ _ hqdC, hd]
      simp
    rw [h1, qrefl_mulVec, herm_smul_left, hb, ← add_smul]
    have h2 : θ + (star θ - 1) / (q : ℂ) * (θ * q) = 1 := by
      field_simp
      linear_combination hθ
    rw [h2, one_smul]
  · intro x hxa hxb
    have hxd : herm H x d = 0 := by
      rw [hd, herm_add_right, herm_smul_right, hxa, hxb]; simp
    rw [← Matrix.mulVec_mulVec, qrefl_mulVec H d, hxd, mul_zero, zero_smul, add_zero, qrefl_mulVec, hxb, mul_zero,
      zero_smul, add_zero]
end Formalism.FourierDecayAlt.P.TwoByOneBlock
