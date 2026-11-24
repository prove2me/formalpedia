-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B5.exp_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:51:39.913826+00:00
-- url     : https://prove2.me/submissions/0537dd43-82b3-4aed-952a-8df951fe3c23

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
namespace Formalism.FourierDecayAlt.P.B5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
section basics
variable {k r : ℕ}
end basics
section setting
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
end setting
section hs
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
end hs
section ck
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
end ck
section phbound
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
end phbound
section calculus
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
private theorem hpk_apply_of_mid_index {k r : ℕ} (i b : Fin (2 * r + k + 1)) (hi : r ≤ i.val ∧ i.val ≤ r + k) :
    Hpk k r i b = if b = i then (if i.val = r + k then -1 else 1) else 0 := by
  have e1 : ¬ (i.val < r ∧ i.val + b.val = 2 * r + k) := by omega
  have e2 : ¬ (b.val < r ∧ i.val + b.val = 2 * r + k) := by omega
  simp only [Hpk, if_neg e1, if_neg e2]
  by_cases hb : b = i
  · subst hb
    simp [hi.1, hi.2]
  · have e3 : ¬ (r ≤ i.val ∧ i.val ≤ r + k ∧ i = b) := fun h => hb h.2.2.symm
    rw [if_neg e3, if_neg hb]
private theorem hpk_apply_of_not_mid_index {k r : ℕ} (i b : Fin (2 * r + k + 1)) (hi : ¬(r ≤ i.val ∧ i.val ≤ r + k)) :
    Hpk k r i b = if b.val = 2 * r + k - i.val then 1 else 0 := by
  have hi1 := i.isLt
  have hb1 := b.isLt
  have e3 : ¬ (r ≤ i.val ∧ i.val ≤ r + k ∧ i = b) := fun h => hi ⟨h.1, h.2.1⟩
  by_cases hb : b.val = 2 * r + k - i.val
  · rw [if_pos hb]
    by_cases h1 : i.val < r
    · have e1 : i.val < r ∧ i.val + b.val = 2 * r + k := ⟨h1, by omega⟩
      simp only [Hpk, if_pos e1]
    · have e1 : ¬ (i.val < r ∧ i.val + b.val = 2 * r + k) := fun h => h1 h.1
      have e2 : b.val < r ∧ i.val + b.val = 2 * r + k := by omega
      simp only [Hpk, if_neg e1, if_pos e2]
  · rw [if_neg hb]
    have e1 : ¬ (i.val < r ∧ i.val + b.val = 2 * r + k) := by omega
    have e2 : ¬ (b.val < r ∧ i.val + b.val = 2 * r + k) := by omega
    simp only [Hpk, if_neg e1, if_neg e2, if_neg e3]
private theorem hpk_mul_self' {k r : ℕ} : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hi1 := i.isLt
  by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
  · rw [Finset.sum_eq_single i]
    · rw [hpk_apply_of_mid_index i i hi, hpk_apply_of_mid_index i j hi, if_pos rfl]
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl, if_pos rfl]
        split_ifs <;> norm_num
      · rw [if_neg (Ne.symm hij), if_neg hij, mul_zero]
    · intro b _ hb
      rw [hpk_apply_of_mid_index i b hi, if_neg hb, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h
  · have hn : 2 * r + k - i.val < 2 * r + k + 1 := by omega
    have hσ : ¬(r ≤ (⟨2 * r + k - i.val, hn⟩ : Fin (2 * r + k + 1)).val ∧
        (⟨2 * r + k - i.val, hn⟩ : Fin (2 * r + k + 1)).val ≤ r + k) := by
      show ¬(r ≤ 2 * r + k - i.val ∧ 2 * r + k - i.val ≤ r + k)
      omega
    have hσσ : 2 * r + k - (⟨2 * r + k - i.val, hn⟩ : Fin (2 * r + k + 1)).val = i.val := by
      show 2 * r + k - (2 * r + k - i.val) = i.val
      omega
    rw [Finset.sum_eq_single ⟨2 * r + k - i.val, hn⟩]
    · rw [hpk_apply_of_not_mid_index i _ hi, hpk_apply_of_not_mid_index _ j hσ, if_pos rfl, one_mul, hσσ]
      by_cases hij : i = j
      · subst hij
        simp
      · rw [if_neg hij, if_neg (fun h => hij (Fin.ext h.symm))]
    · intro b _ hb
      have hb' : ¬ b.val = 2 * r + k - i.val := fun h => hb (Fin.ext h)
      rw [hpk_apply_of_not_mid_index i b hi, if_neg hb', zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
end calculus
section adj
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
end adj
end Formalism.FourierDecayAlt.P.B5
end
end

set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.B5
theorem _root_.solution {X : Mat k r} (hX : inLie k r X) (t : ℝ) : NormedSpace.exp ((t : ℂ) • X) ∈ GV k r := by
  have hH : Hpk k r * Hpk k r = 1 := hpk_mul_self'
  have hdet : (Hpk k r).det * (Hpk k r).det = 1 := by rw [← Matrix.det_mul, hH, Matrix.det_one]
  have hu : IsUnit (Hpk k r) := by
    first
    | exact (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse hH)
    | exact (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_eq_one _ _ hdet)
    | exact (Matrix.isUnit_iff_isUnit_det _).2 (IsUnit.of_mul_eq_one _ hdet)
    | exact (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (left_ne_zero_of_mul_eq_one hdet))
  have hinv : (Hpk k r)⁻¹ = Hpk k r := Matrix.inv_eq_left_inv hH
  have e : Xᴴ * Hpk k r = -(Hpk k r * X) := eq_neg_of_add_eq_zero_left hX
  have hXh : Xᴴ = Hpk k r * (-X) * (Hpk k r)⁻¹ := by
    rw [hinv]
    calc Xᴴ = Xᴴ * Hpk k r * Hpk k r := by rw [Matrix.mul_assoc, hH, Matrix.mul_one]
      _ = Hpk k r * (-X) * Hpk k r := by rw [e, Matrix.mul_neg]
  have hs : ((t : ℂ) • X)ᴴ = Hpk k r * ((t : ℂ) • -X) * (Hpk k r)⁻¹ := by
    rw [Matrix.conjTranspose_smul, hXh, Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    exact Complex.conj_ofReal t
  have hE : (NormedSpace.exp ((t : ℂ) • X))ᴴ = NormedSpace.exp (((t : ℂ) • X)ᴴ) := by
    first
    | exact (Matrix.exp_conjTranspose _).symm
    | exact Matrix.exp_conjTranspose _
  have hEE : NormedSpace.exp ((t : ℂ) • -X) * NormedSpace.exp ((t : ℂ) • X) = 1 := by
    rw [smul_neg, ← Matrix.exp_add_of_commute _ _ ((Commute.refl ((t : ℂ) • X)).neg_left), neg_add_cancel,
      NormedSpace.exp_zero]
  show (NormedSpace.exp ((t : ℂ) • X))ᴴ * Hpk k r * NormedSpace.exp ((t : ℂ) • X) = Hpk k r
  rw [hE, hs, Matrix.exp_conj _ _ hu, hinv, Matrix.mul_assoc (Hpk k r * _) (Hpk k r), hH, Matrix.mul_one,
    Matrix.mul_assoc, hEE, Matrix.mul_one]
end Formalism.FourierDecayAlt.P.B5
