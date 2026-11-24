-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.dg_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:55:42.364212+00:00
-- url     : https://prove2.me/submissions/5caa334b-d348-444f-91c6-9554db4710d8

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_inv_mem_I
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
    ‖dg k r t i‖ ≤ 2 ^ r := by
  obtain ⟨h1, h2⟩ := ht
  have hpos : 0 < t := by linarith
  have hi := i.isLt
  unfold dg
  split_ifs with ha hb
  · rw [normc_lemma, abs_of_pos (pow_pos hpos _)]
    exact le_trans (pow_le_pow_left₀ hpos.le h2 _) (two_pow_le _ (by omega))
  · rw [norm_one]
    exact one_le_pow₀ (by norm_num)
  · rw [normc_lemma, ← inv_pow, abs_of_pos (pow_pos (inv_pos.mpr hpos) _)]
    exact le_trans (pow_le_pow_left₀ (inv_pos.mpr hpos).le (inv_mem_I ⟨h1, h2⟩).2 _)
      (two_pow_le _ (by omega))
end Formalism.FourierDecayAlt.P.B4
