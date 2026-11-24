-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.hermitian_matrix_three_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:11:21.371021+00:00
-- url     : https://prove2.me/submissions/6936f7a5-3222-4412-b88b-671fa8340eae

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_tk_mulVec
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_eq_three_block_of_coordinates

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x8
theorem _root_.solution (a b : ℂ) (y : Fin (2 * r' + k + 1) → ℂ) :
    Hpk k (1 + r') *ᵥ mk3 k r' a y b = mk3 k r' b (Hpk k r' *ᵥ y) a := by
  apply eq_three_block_of_coordinates
  · rw [tk_mulVec]
    have h1 : Hpk k (1 + r') (tkF k r') (tkF k r') = 0 := by
      unfold Hpk tkF
      dsimp only
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    have h2 : ∀ j, Hpk k (1 + r') (tkF k r') (levPos k 1 r' j) = 0 := by
      intro j; have := j.isLt
      unfold Hpk tkF levPos
      dsimp only
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    have h3 : Hpk k (1 + r') (tkF k r') (tkL k r') = 1 := by
      unfold Hpk tkF tkL
      dsimp only
      rw [if_pos (by omega)]
    simp [h1, h2, h3]
  · intro i
    have hi := i.isLt
    rw [tk_mulVec]
    have h1 : Hpk k (1 + r') (levPos k 1 r' i) (tkF k r') = 0 := by
      unfold Hpk tkF levPos
      dsimp only
      rw [if_neg (by omega), if_neg (by omega), if_neg (by rw [Fin.ext_iff]; dsimp only; omega)]
    have h2 : ∀ j, Hpk k (1 + r') (levPos k 1 r' i) (levPos k 1 r' j) = Hpk k r' i j := by
      intro j; have := j.isLt
      unfold Hpk levPos
      dsimp only
      have c1 : (i.val + 1 < 1 + r' ∧ i.val + 1 + (j.val + 1) = 2 * (1 + r') + k) ↔ (i.val < r' ∧ i.val + j.val = 2 * r' + k) := by omega
      have c2 : (j.val + 1 < 1 + r' ∧ i.val + 1 + (j.val + 1) = 2 * (1 + r') + k) ↔ (j.val < r' ∧ i.val + j.val = 2 * r' + k) := by omega
      have c3 : (1 + r' ≤ i.val + 1 ∧ i.val + 1 ≤ 1 + r' + k ∧
          (⟨i.val + 1, by omega⟩ : Fin (2 * (1 + r') + k + 1)) = ⟨j.val + 1, by omega⟩) ↔ (r' ≤ i.val ∧ i.val ≤ r' + k ∧ i = j) := by
        rw [Fin.ext_iff, Fin.ext_iff]; dsimp only; omega
      have c4 : (i.val + 1 = 1 + r' + k) ↔ (i.val = r' + k) := by omega
      simp only [c1, c2, c3, c4]
    have h3 : Hpk k (1 + r') (levPos k 1 r' i) (tkL k r') = 0 := by
      unfold Hpk tkL levPos
      dsimp only
      rw [if_neg (by omega), if_neg (by omega), if_neg (by rw [Fin.ext_iff]; dsimp only; omega)]
    simp [h1, h2, h3, Matrix.mulVec, dotProduct]
  · rw [tk_mulVec]
    have h1 : Hpk k (1 + r') (tkL k r') (tkF k r') = 1 := by
      unfold Hpk tkF tkL
      dsimp only
      rw [if_neg (by omega), if_pos (by omega)]
    have h2 : ∀ j, Hpk k (1 + r') (tkL k r') (levPos k 1 r' j) = 0 := by
      intro j; have := j.isLt
      unfold Hpk tkL levPos
      dsimp only
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    have h3 : Hpk k (1 + r') (tkL k r') (tkL k r') = 0 := by
      unfold Hpk tkL
      dsimp only
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    simp [h1, h2, h3]
end Formalism.FourierDecayAlt.P.B2x8
