-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.Bd.smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:55:44.579982+00:00
-- url     : https://prove2.me/submissions/88fc9312-3c09-4bb2-b00d-0677bb4393ff

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WirtingerIntegrationByParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_gen_Bd_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
open Formalism.FourierDecayAlt.G MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
namespace Bd
theorem _root_.solution {𝕜' V : Type*} [NormedField 𝕜'] [NormedAlgebra ℝ 𝕜'] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedSpace 𝕜' V] [IsScalarTower ℝ 𝕜' V] {f : E → 𝕜'} {h : E → V} {s : Set E} {x : E} {n : ℕ} {A B P : ℝ}
    (hs : IsOpen s) (hx : x ∈ s) (hP : 0 ≤ P) (hf : ContDiffOn ℝ n f s) (hh : ContDiffOn ℝ n h s)
    (bf : Bd f s x n A P) (bh : Bd h s x n B P) :
    Bd (fun y => f y • h y) s x n (2 ^ n * A * B) P := by
  intro j hj
  have hA : 0 ≤ A := gen_Bd_nonneg bf
  have hB : 0 ≤ B := gen_Bd_nonneg bh
  have h1 := norm_iteratedFDerivWithin_smul_le hf hh hs.uniqueDiffOn hx (n := j) (by exact_mod_cast hj)
  refine h1.trans ?_
  have h2 : ∀ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i f s x‖ *
      ‖iteratedFDerivWithin ℝ (j - i) h s x‖ ≤ (j.choose i : ℝ) * (A * B * P ^ j) := by
    intro i hi
    have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have e1 := bf i (hij.trans hj)
    have e2 := bh (j - i) ((Nat.sub_le j i).trans hj)
    have e3 : P ^ j = P ^ i * P ^ (j - i) := by rw [← pow_add, Nat.add_sub_cancel' hij]
    have e4 : ‖iteratedFDerivWithin ℝ i f s x‖ * ‖iteratedFDerivWithin ℝ (j - i) h s x‖ ≤
        (A * P ^ i) * (B * P ^ (j - i)) :=
      mul_le_mul e1 e2 (norm_nonneg _) (mul_nonneg hA (pow_nonneg hP _))
    calc (j.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i f s x‖ * ‖iteratedFDerivWithin ℝ (j - i) h s x‖
        = (j.choose i : ℝ) * (‖iteratedFDerivWithin ℝ i f s x‖ * ‖iteratedFDerivWithin ℝ (j - i) h s x‖) := by ring
      _ ≤ (j.choose i : ℝ) * ((A * P ^ i) * (B * P ^ (j - i))) :=
          mul_le_mul_of_nonneg_left e4 (Nat.cast_nonneg _)
      _ = (j.choose i : ℝ) * (A * B * P ^ j) := by rw [e3]; ring
  refine (Finset.sum_le_sum h2).trans ?_
  rw [← Finset.sum_mul]
  have h3 : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) = 2 ^ j := by
    exact_mod_cast Nat.sum_range_choose j
  rw [h3]
  have h4 : (2 : ℝ) ^ j ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hj
  have h5 : 0 ≤ A * B * P ^ j := mul_nonneg (mul_nonneg hA hB) (pow_nonneg hP _)
  calc (2 : ℝ) ^ j * (A * B * P ^ j) ≤ 2 ^ n * (A * B * P ^ j) := mul_le_mul_of_nonneg_right h4 h5
    _ = 2 ^ n * A * B * P ^ j := by ring
end Bd
end Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
