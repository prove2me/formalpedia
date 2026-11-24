-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B5.dil_mem_N
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:26:30.932277+00:00
-- url     : https://prove2.me/submissions/1d335f6c-4ca6-40fa-8378-d40435cf1e5a

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_aDil_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2_aDil_inv

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
private theorem mul_mem_uh {ι : Type*} [Fintype ι] [DecidableEq ι] {H a b : Matrix ι ι ℂ}
    (ha : a ∈ UH H) (hb : b ∈ UH H) : a * b ∈ UH H := by
  show (a * b)ᴴ * H * (a * b) = H
  have ha' : aᴴ * H * a = H := ha
  have hb' : bᴴ * H * b = H := hb
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * H * (a * b) = bᴴ * (aᴴ * H * a) * b := by simp only [Matrix.mul_assoc]
    _ = H := by rw [ha', hb']
private theorem star_aDil_entry_mul_aDil_entry_eq_one {k r : ℕ} (t : ℝ) (ht : t ≠ 0) (i j : Fin (2 * r + k + 1))
    (h : Hpk k r i j ≠ 0) :
    star (if i.val < r then ((t ^ (r - i.val) : ℝ) : ℂ) else if i.val ≤ r + k then 1
      else (((t ^ (i.val - (r + k)))⁻¹ : ℝ) : ℂ)) *
    (if j.val < r then ((t ^ (r - j.val) : ℝ) : ℂ) else if j.val ≤ r + k then 1
      else (((t ^ (j.val - (r + k)))⁻¹ : ℝ) : ℂ)) = 1 := by
  by_cases hA : i.val < r ∧ i.val + j.val = 2 * r + k
  · have e1 : ¬ j.val < r := by omega
    have e2 : ¬ j.val ≤ r + k := by omega
    have e3 : j.val - (r + k) = r - i.val := by omega
    rw [if_pos hA.1, if_neg e1, if_neg e2, e3]
    rw [show star ((t ^ (r - i.val) : ℝ) : ℂ) = ((t ^ (r - i.val) : ℝ) : ℂ) from Complex.conj_ofReal _]
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ (pow_ne_zero _ ht), Complex.ofReal_one]
  by_cases hB : j.val < r ∧ i.val + j.val = 2 * r + k
  · have e1 : ¬ i.val < r := by omega
    have e2 : ¬ i.val ≤ r + k := by omega
    have e3 : i.val - (r + k) = r - j.val := by omega
    rw [if_neg e1, if_neg e2, if_pos hB.1, e3]
    rw [show star (((t ^ (r - j.val))⁻¹ : ℝ) : ℂ) = (((t ^ (r - j.val))⁻¹ : ℝ) : ℂ) from
      Complex.conj_ofReal _]
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ (pow_ne_zero _ ht), Complex.ofReal_one]
  by_cases hC : r ≤ i.val ∧ i.val ≤ r + k ∧ i = j
  · obtain ⟨hC1, hC2, rfl⟩ := hC
    rw [if_neg (not_lt.2 hC1), if_pos hC2]
    simp
  · exfalso
    apply h
    unfold Hpk
    rw [if_neg hA, if_neg hB, if_neg hC]
private theorem aDil_mem_gv {k r : ℕ} (t : ℝ) (ht : t ≠ 0) : aDil k r t ∈ GV k r := by
  show (aDil k r t)ᴴ * Hpk k r * aDil k r t = Hpk k r
  unfold aDil
  rw [Matrix.diagonal_conjTranspose]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Pi.star_apply]
  by_cases hH : Hpk k r i j = 0
  · rw [hH]
    simp
  · have h1 := star_aDil_entry_mul_aDil_entry_eq_one t ht i j hH
    linear_combination (Hpk k r i j) * h1
private theorem aDil_inv_mul_aDil {k r : ℕ} (t : ℝ) (ht : t ≠ 0) : aDil k r t⁻¹ * aDil k r t = 1 := by
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  unfold aDil
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  split_ifs
  · push_cast
    rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero _ htc)]
  · simp
  · push_cast
    rw [inv_pow, inv_inv, mul_inv_cancel₀ (pow_ne_zero _ htc)]
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
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.B5
theorem _root_.solution (t : ℝ) (ht : t ≠ 0) {n : Mat k r} (hn : n ∈ Nset k r) :
    aDil k r t * n * (aDil k r t)⁻¹ ∈ Nset k r := by
  set d : Fin (2 * r + k + 1) → ℂ := fun i => if i.val < r then ((t ^ (r - i.val) : ℝ) : ℂ)
    else if i.val ≤ r + k then 1 else (((t ^ (i.val - (r + k)))⁻¹ : ℝ) : ℂ) with hd_def
  set d' : Fin (2 * r + k + 1) → ℂ := fun i => if i.val < r then ((t⁻¹ ^ (r - i.val) : ℝ) : ℂ)
    else if i.val ≤ r + k then 1 else (((t⁻¹ ^ (i.val - (r + k)))⁻¹ : ℝ) : ℂ) with hd'_def
  have hA : aDil k r t = Matrix.diagonal d := rfl
  have hA' : aDil k r t⁻¹ = Matrix.diagonal d' := rfl
  have m1 : Matrix.diagonal d ∈ UH (Hpk k r) := aDil_mem_gv t ht
  have m2 : Matrix.diagonal d' ∈ UH (Hpk k r) := aDil_mem_gv t⁻¹ (inv_ne_zero ht)
  have hdd : ∀ i, d i * d' i = 1 := by
    intro i
    have h1 := congrArg (fun M : Mat k r => M i i) (aDil_inv_mul_aDil (k := k) (r := r) t ht)
    simp only [hA, hA', Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq,
      Matrix.one_apply_eq] at h1
    rw [mul_comm]
    exact h1
  rw [aDil_inv k r t ht, hA, hA']
  unfold QuantumDeterminants.Nset at hn ⊢
  obtain ⟨hU, hcol, hmid⟩ := hn
  rw [Set.mem_setOf_eq]
  refine ⟨mul_mem_uh (mul_mem_uh m1 hU) m2, ?_, ?_⟩
  · intro a i hai
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, hcol a i hai]
    split_ifs with h
    · subst h
      rw [mul_one]
      exact hdd _
    · simp
  · intro i j hj1 hj2 hi
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, hmid i j hj1 hj2 hi]
    split_ifs with h
    · subst h
      rw [mul_one]
      exact hdd _
    · simp
end Formalism.FourierDecayAlt.P.B5
