-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.frame_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:56:40.866586+00:00
-- url     : https://prove2.me/submissions/4b310451-1fc2-488c-bad8-c4a457439d9c

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_Frame_mp
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_Frame_card_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_Frame_card_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_Frame_reindex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormFactor
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {m P Q : Type} [Fintype m] [DecidableEq m] [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
variable {H : Matrix m m ℂ} {Ep : Matrix m P ℂ} {Em : Matrix m Q ℂ}
namespace Formalism.FourierDecayAlt.P.HermitianFormFactor
theorem _root_.solution (hH : H.IsHermitian) (h2 : H * H = 1) (a b : ℕ) (hab : Fintype.card m = a + b)
    (htr : H.trace = (a : ℂ) - b) :
    ∃ (Ep : Matrix m (Fin a) ℂ) (Em : Matrix m (Fin b) ℂ), Frame H Ep Em := by
  classical
  set U : Matrix m m ℂ := (hH.eigenvectorUnitary : Matrix m m ℂ) with hU
  set lam : m → ℝ := hH.eigenvalues with hlam
  have hU1 : Uᴴ * U = 1 := by
    have := Unitary.coe_star_mul_self hH.eigenvectorUnitary
    simpa [Matrix.star_eq_conjTranspose] using this
  have hU2 : U * Uᴴ = 1 := by
    have := Unitary.coe_mul_star_self hH.eigenvectorUnitary
    simpa [Matrix.star_eq_conjTranspose] using this
  have hspec : H = U * Matrix.diagonal (fun i => (lam i : ℂ)) * Uᴴ := by
    have := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  set D : Matrix m m ℂ := Matrix.diagonal (fun i => (lam i : ℂ)) with hD
  have hDD : D * D = 1 := by
    have e1 : D = Uᴴ * H * U := by
      rw [hspec]
      have : Uᴴ * (U * D * Uᴴ) * U = (Uᴴ * U) * D * (Uᴴ * U) := by simp only [Matrix.mul_assoc]
      rw [this, hU1]; simp
    have e2 : D * D = Uᴴ * (H * (U * Uᴴ) * H) * U := by
      conv_lhs => rw [e1]
      simp only [Matrix.mul_assoc]
    rw [e2, hU2, Matrix.mul_one, h2, Matrix.mul_one, hU1]
  have hl : ∀ i, lam i = 1 ∨ lam i = -1 := by
    intro i
    have := congrFun (congrFun hDD i) i
    rw [hD, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at this
    have h3 : lam i * lam i = 1 := by exact_mod_cast this
    exact mul_self_eq_one_iff.mp h3
  let p : m → Prop := fun i => lam i = 1
  let Ep₀ : Matrix m {i // p i} ℂ := U.submatrix id Subtype.val
  let Em₀ : Matrix m {i // ¬ p i} ℂ := U.submatrix id Subtype.val
  have F₀ : Frame H Ep₀ Em₀ := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have : Ep₀ᴴ * Ep₀ = (Uᴴ * U).submatrix Subtype.val Subtype.val := rfl
      rw [this, hU1]
      exact Matrix.submatrix_one _ Subtype.val_injective
    · have : Em₀ᴴ * Em₀ = (Uᴴ * U).submatrix Subtype.val Subtype.val := rfl
      rw [this, hU1]
      exact Matrix.submatrix_one _ Subtype.val_injective
    · have : Ep₀ᴴ * Em₀ = (Uᴴ * U).submatrix Subtype.val Subtype.val := rfl
      rw [this, hU1]
      ext i j
      have hne : i.val ≠ j.val := fun h => j.2 (h ▸ i.2)
      simp [hne]
    · ext i j
      have e := Fintype.sum_subtype_add_sum_subtype p (fun l => U i l * star (U j l))
      have e3 : (U * Uᴴ) i j = ∑ l, U i l * star (U j l) := by
        simp [Matrix.mul_apply]
      rw [← hU2, e3, ← e]
      simp [Matrix.mul_apply, Ep₀, Em₀]
    · ext i j
      have e := Fintype.sum_subtype_add_sum_subtype p (fun l => U i l * (lam l : ℂ) * star (U j l))
      have e3 : H i j = ∑ l, U i l * (lam l : ℂ) * star (U j l) := by
        conv_lhs => rw [hspec]
        simp [Matrix.mul_apply, hD, Matrix.diagonal_apply]
      rw [e3, ← e]
      have s1 : ∑ l : {l // p l}, U i l * (lam l : ℂ) * star (U j l) = ∑ l : {l // p l}, U i l * star (U j l) := by
        refine Finset.sum_congr rfl fun l _ => ?_
        have : lam l = 1 := l.2
        rw [this]; simp
      have s2 : ∑ l : {l // ¬ p l}, U i l * (lam l : ℂ) * star (U j l) = - ∑ l : {l // ¬ p l}, U i l * star (U j l) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun l _ => ?_
        have : lam l = -1 := (hl l).resolve_left l.2
        rw [this]; simp
      rw [s1, s2]
      simp [Matrix.mul_apply, Ep₀, Em₀, sub_eq_add_neg]
  have c1 := F₀.card_add
  have c2 := F₀.card_sub
  rw [hab] at c1
  rw [htr] at c2
  have hcP : Fintype.card {i // p i} = a := by
    have : ((Fintype.card {i // p i} : ℕ) : ℂ) = (a : ℂ) := by
      push_cast at c1
      linear_combination (1 / 2 : ℂ) * c1 + (1 / 2 : ℂ) * c2
    exact_mod_cast this
  have hcQ : Fintype.card {i // ¬ p i} = b := by
    have : ((Fintype.card {i // ¬ p i} : ℕ) : ℂ) = (b : ℂ) := by
      push_cast at c1
      linear_combination (1 / 2 : ℂ) * c1 - (1 / 2 : ℂ) * c2
    exact_mod_cast this
  exact ⟨_, _, F₀.reindex (Fintype.equivFinOfCardEq hcP).symm (Fintype.equivFinOfCardEq hcQ).symm⟩
end Formalism.FourierDecayAlt.P.HermitianFormFactor
