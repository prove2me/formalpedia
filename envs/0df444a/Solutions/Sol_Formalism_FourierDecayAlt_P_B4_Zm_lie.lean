-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.Zm_lie
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:34:25.885357+00:00
-- url     : https://prove2.me/submissions/ad7bf5fc-8ad4-444d-a35c-5152e511af98

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
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
private lemma zd_pair_lemma (i j : Fin (2 * r + k + 1)) (hi : i.val < r)
    (hij : i.val + j.val = 2 * r + k) : zd k r i + zd k r j = 0 := by
  have hj1 : ¬ j.val < r := by omega
  have hj2 : ¬ j.val ≤ r + k := by omega
  have e : j.val - (r + k) = r - i.val := by omega
  unfold zd
  rw [if_pos hi, if_neg hj1, if_neg hj2, e]
  ring
private lemma zd_mid_lemma_2 (i : Fin (2 * r + k + 1)) (h1 : r ≤ i.val) (h2 : i.val ≤ r + k) :
    zd k r i = 0 := by
  unfold zd
  rw [if_neg (by omega), if_pos h2]
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
theorem _root_.solution : inLie k r (Zm k r) := by
  unfold inLie
  have hD : (Zm k r)ᴴ = Zm k r := by
    unfold Zm
    ext i j
    rw [Matrix.conjTranspose_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
    by_cases h : i = j
    · subst h
      rw [if_pos rfl]
      simp
    · rw [if_neg (Ne.symm h), if_neg h, star_zero]
  rw [hD]
  ext i j
  rw [Matrix.add_apply, Matrix.zero_apply]
  unfold Zm
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  have hi := i.isLt
  have hj := j.isLt
  unfold Hpk
  split_ifs with h1 h2 h3 h4
  · rw [mul_one, one_mul, ← Complex.ofReal_add, zd_pair_lemma i j h1.1 h1.2, Complex.ofReal_zero]
  · rw [mul_one, one_mul, ← Complex.ofReal_add, add_comm, zd_pair_lemma j i h2.1 (by omega),
      Complex.ofReal_zero]
  · obtain ⟨ha, hb, rfl⟩ := h3
    rw [zd_mid_lemma_2 i ha hb]
    simp
  · obtain ⟨ha, hb, rfl⟩ := h3
    rw [zd_mid_lemma_2 i ha hb]
    simp
  · simp
end Formalism.FourierDecayAlt.P.B4
