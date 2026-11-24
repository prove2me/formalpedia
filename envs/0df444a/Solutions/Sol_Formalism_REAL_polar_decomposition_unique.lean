-- Prove2me | solution 1 for Formalism.REAL.polar_decomposition_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:57:42.131812+00:00
-- url     : https://prove2.me/submissions/465b5c30-6bd6-4412-b9da-ffe97b56fa13

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IndefiniteUnitaryPreservesForm
import Theorems.Thm_Formalism_REAL_exp_injective_hermitian
import Theorems.Thm_Formalism_REAL_exp_conjTranspose_of_hermitian
import Theorems.Thm_Formalism_REAL_matrix_exp_mul_exp_neg
import Theorems.Thm_Formalism_REAL_exp_add_self
import Theorems.Thm_Formalism_REAL_eq_of_add_self_eq_add_self
import Theorems.Thm_Formalism_REAL_hermitian_of_mem_hermitian_part

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder
noncomputable section
open Formalism Formalism.REAL
variable {n : ℕ}
namespace Formalism.REAL
theorem _root_.solution {ε : Fin n → Bool} (k k' X X' : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Kset ε)
    (hk' : k' ∈ Kset ε) (hX : inP ε X) (hX' : inP ε X')
    (h : k * NormedSpace.exp X = k' * NormedSpace.exp X') : k = k' ∧ X = X' := by
  have hXh := hermitian_of_mem_hermitian_part hX
  have hX'h := hermitian_of_mem_hermitian_part hX'
  have hk1 : k ∈ unitaryGroup (Fin n) ℂ := by
    unfold Kset at hk
    exact hk.1
  have hk1' : k' ∈ unitaryGroup (Fin n) ℂ := by
    unfold Kset at hk'
    exact hk'.1
  have hu : star k * k = 1 := Matrix.mem_unitaryGroup_iff'.mp hk1
  have hu' : star k' * k' = 1 := Matrix.mem_unitaryGroup_iff'.mp hk1'
  have key : ∀ (c Y : Matrix (Fin n) (Fin n) ℂ), star c * c = 1 →
      (NormedSpace.exp Y)ᴴ = NormedSpace.exp Y →
      (c * NormedSpace.exp Y)ᴴ * (c * NormedSpace.exp Y) = NormedSpace.exp (Y + Y) := by
    intro c Y hc hY
    rw [Matrix.conjTranspose_mul, hY, exp_add_self]
    calc NormedSpace.exp Y * cᴴ * (c * NormedSpace.exp Y)
        = NormedSpace.exp Y * (star c * c) * NormedSpace.exp Y := by
          rw [Matrix.star_eq_conjTranspose]
          simp only [mul_assoc]
      _ = _ := by rw [hc, mul_one]
  have h2 : NormedSpace.exp (X + X) = NormedSpace.exp (X' + X') := by
    rw [← key k X hu (exp_conjTranspose_of_hermitian hXh), ← key k' X' hu' (exp_conjTranspose_of_hermitian hX'h), h]
  have hXX : X = X' := eq_of_add_self_eq_add_self (exp_injective_hermitian (by rw [Matrix.conjTranspose_add, hXh])
    (by rw [Matrix.conjTranspose_add, hX'h]) h2)
  subst hXX
  refine ⟨?_, rfl⟩
  calc k = k * NormedSpace.exp X * NormedSpace.exp (-X) := by
        rw [mul_assoc, matrix_exp_mul_exp_neg, mul_one]
    _ = k' * NormedSpace.exp X * NormedSpace.exp (-X) := by rw [h]
    _ = k' := by rw [mul_assoc, matrix_exp_mul_exp_neg, mul_one]
end Formalism.REAL
