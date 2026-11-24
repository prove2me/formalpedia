-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.aDil_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:51:22.679115+00:00
-- url     : https://prove2.me/submissions/25d700bf-9ee7-4d29-80cb-ab8dfba97a91

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_aDil_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_dg_mid
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
private lemma dg_pair_lemma (k r : ℕ) (t : ℝ) (ht : t ≠ 0) (i j : Fin (2 * r + k + 1))
    (hi : i.val < r) (hij : i.val + j.val = 2 * r + k) : dg k r t i * dg k r t j = 1 := by
  have hj1 : ¬ j.val < r := by omega
  have hj2 : ¬ j.val ≤ r + k := by omega
  have e : j.val - (r + k) = r - i.val := by omega
  unfold dg
  rw [if_pos hi, if_neg hj1, if_neg hj2, e, ← Complex.ofReal_mul,
    mul_inv_cancel₀ (pow_ne_zero _ ht), Complex.ofReal_one]
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
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
namespace Formalism.FourierDecayAlt.P.B4
theorem _root_.solution (k r : ℕ) (t : ℝ) (ht : t ≠ 0) : aDil k r t ∈ GV k r := by
  show (aDil k r t)ᴴ * Hpk k r * aDil k r t = Hpk k r
  have hs : ∀ l, star (dg k r t l) = dg k r t l := by
    intro l
    unfold dg
    split_ifs <;> simp
  have hD : (Matrix.diagonal (dg k r t))ᴴ = Matrix.diagonal (dg k r t) := by
    ext i j
    rw [Matrix.conjTranspose_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
    by_cases h : i = j
    · subst h
      rw [if_pos rfl]
      exact hs i
    · rw [if_neg (Ne.symm h), if_neg h, star_zero]
  rw [aDil_eq, hD]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hi := i.isLt
  have hj := j.isLt
  unfold Hpk
  split_ifs with h1 h2 h3 h4
  · rw [mul_one, dg_pair_lemma k r t ht i j h1.1 h1.2]
  · rw [mul_one, mul_comm, dg_pair_lemma k r t ht j i h2.1 (by omega)]
  · obtain ⟨ha, hb, rfl⟩ := h3
    rw [dg_mid k r t i ha hb]
    simp
  · obtain ⟨ha, hb, rfl⟩ := h3
    rw [dg_mid k r t i ha hb]
    simp
  · rw [mul_zero, zero_mul]
end Formalism.FourierDecayAlt.P.B4
