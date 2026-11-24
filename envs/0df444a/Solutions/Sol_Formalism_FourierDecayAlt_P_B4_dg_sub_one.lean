-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.dg_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:13:56.925801+00:00
-- url     : https://prove2.me/submissions/c6db5881-ba77-4b8b-9b62-41804c45c5e0

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_inv_mem_I
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_abs_inv_sub_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_pow_sub_one_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_two_pow_le
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Filter Topology
noncomputable section
namespace Formalism.FourierDecayAlt.P.B4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
private lemma normc_lemma (x : ℝ) : ‖(x : ℂ)‖ = |x| := by
  rw [Complex.norm_real, Real.norm_eq_abs]
section
variable {t : ℝ × ℝ} (h1 : t.1 ∈ Set.Icc (1 / 2 : ℝ) 2) (h2 : t.2 ∈ Set.Icc (1 / 2 : ℝ) 2)
include h1 h2
end
end Formalism.FourierDecayAlt.P.B4
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4
end Formalism.FourierDecayAlt.P
end
end

set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.B4
theorem _root_.solution {t : ℝ} (ht : t ∈ Set.Icc (1 / 2 : ℝ) 2) (i : Fin (2 * r + k + 1)) :
    ‖dg k r t i - 1‖ ≤ 2 ^ (r + 1) * |t - 1| := by
  have ht' := ht
  obtain ⟨h1, h2⟩ := ht
  have hpos : 0 < t := by linarith
  have hi := i.isLt
  have hA : 0 ≤ |t - 1| := abs_nonneg _
  have h5 : (2 : ℝ) ^ (r + 1) = 2 ^ r * 2 := pow_succ 2 r
  have h6 : (1 : ℝ) ≤ 2 ^ r := one_le_pow₀ (by norm_num)
  rw [h5]
  unfold dg
  split_ifs with ha hb
  · rw [← Complex.ofReal_one, ← Complex.ofReal_sub, normc_lemma]
    have h3 := pow_sub_one_le hpos.le h2 (r - i.val)
    have h4 : (2 : ℝ) ^ (r - i.val) ≤ 2 ^ r := two_pow_le _ (by omega)
    have h7 := mul_le_mul_of_nonneg_right (show (2 : ℝ) ^ (r - i.val) - 1 ≤ 2 ^ r * 2 by linarith) hA
    linarith
  · rw [sub_self, norm_zero]
    positivity
  · rw [← Complex.ofReal_one, ← Complex.ofReal_sub, normc_lemma, ← inv_pow]
    have hinv := inv_mem_I ht'
    have h3 := pow_sub_one_le (inv_pos.mpr hpos).le hinv.2 (i.val - (r + k))
    have h4 : (2 : ℝ) ^ (i.val - (r + k)) ≤ 2 ^ r := two_pow_le _ (by omega)
    have h8 := abs_inv_sub_one ht'
    have h9 : (1 : ℝ) ≤ 2 ^ (i.val - (r + k)) := one_le_pow₀ (by norm_num)
    have h10 := mul_le_mul_of_nonneg_left h8 (show (0 : ℝ) ≤ 2 ^ (i.val - (r + k)) - 1 by linarith)
    have h11 := mul_le_mul_of_nonneg_right h4 hA
    nlinarith
end Formalism.FourierDecayAlt.P.B4
