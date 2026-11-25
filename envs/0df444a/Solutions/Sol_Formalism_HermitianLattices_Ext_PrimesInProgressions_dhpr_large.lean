-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.dhpr_large
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:57:27.204276+00:00
-- url     : https://prove2.me/submissions/82b6252a-dd64-44df-84a3-633f70866d24

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHPrimeC
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHPrimeD
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_dhpr_block
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_dhpr_blocks
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_dhpr_esum
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_dhpr_wsum
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_dhpr_wsup


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet
open LSeries ArithmeticFunction DirichletCharacter
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution {M : ℕ} [NeZero M] (χ₁ : DirichletCharacter ℂ M) (h1 : χ₁ ^ 2 = 1) (k : ℕ)
    {σ η : ℝ} (hσ : 1 ≤ σ) (hση : σ - 1 = η) (hη : 0 < η) (hη1 : η ≤ 1) (v0 V : ℕ) (hV : v0 ≤ V)
    {A CH : ℝ} (hA : 0 ≤ A) (hCH : 0 ≤ CH)
    (hHyp : ∀ v : ℕ, ∑ n ∈ Ioc ⌊Real.exp (v : ℝ)⌋₊ ⌊Real.exp ((v + 1 : ℕ) : ℝ)⌋₊,
        (∑ d ∈ n.divisors, χ₁ (d : ZMod M)).re / (n : ℝ) ≤
          A + CH * M * (((v : ℝ) + 1) * Real.exp (-((v : ℝ) / 2)))) :
    ∑ n ∈ Ioc ⌊Real.exp (v0 : ℝ)⌋₊ ⌊Real.exp (V : ℝ)⌋₊, dhprF χ₁ k σ n ≤
      2 * A * (2 * Real.exp 2 * ((k : ℝ) + 2) * (((k : ℝ) + 1) * k.factorial) / η ^ (k + 2))
      + 2 * CH * M * (Real.exp 1 * (((k : ℝ) + 1) * k.factorial) / η ^ (k + 1) *
          (20 * Real.exp (-((v0 : ℝ) / 4)))) := by
  have hw : ∀ v : ℕ, ((v : ℝ) + 1) ^ (k + 1) * Real.exp (-(η * v)) ≤
      Real.exp 1 * (((k : ℝ) + 1) * k.factorial) / η ^ (k + 1) := by
    intro v
    have h := dhpr_wsup (k + 1) hη hη1 v
    rw [Nat.factorial_succ] at h
    push_cast at h
    exact h
  have hS : ∑ v ∈ Ico v0 V, ((v : ℝ) + 1) ^ (k + 1) * Real.exp (-(η * v)) ≤
      2 * Real.exp 2 * ((k : ℝ) + 2) * (((k : ℝ) + 1) * k.factorial) / η ^ (k + 2) := by
    have h := dhpr_wsum (k + 1) hη hη1 v0 V
    rw [Nat.factorial_succ] at h
    push_cast at h
    refine h.trans (le_of_eq ?_)
    ring
  have hE := dhpr_esum v0 V
  have hA2 : 0 ≤ 2 * A := mul_nonneg (by norm_num) hA
  have hC2 : 0 ≤ 2 * CH * (M : ℝ) := mul_nonneg (mul_nonneg (by norm_num) hCH) (Nat.cast_nonneg _)
  have hK : 0 ≤ Real.exp 1 * (((k : ℝ) + 1) * k.factorial) / η ^ (k + 1) :=
    div_nonneg (by positivity) (pow_nonneg hη.le _)
  rw [dhpr_blocks _ v0 V hV]
  calc _ ≤ ∑ v ∈ Ico v0 V, (2 * A * (((v : ℝ) + 1) ^ (k + 1) * Real.exp (-(η * v))) +
        2 * CH * M * ((((v : ℝ) + 1) ^ (k + 1) * Real.exp (-(η * v))) *
          (((v : ℝ) + 1) * Real.exp (-((v : ℝ) / 2))))) := by
        apply Finset.sum_le_sum
        intro v _
        have h := dhpr_block χ₁ h1 k hσ v _ (hHyp v)
        rw [hση] at h
        refine h.trans (le_of_eq ?_)
        ring
    _ = 2 * A * ∑ v ∈ Ico v0 V, (((v : ℝ) + 1) ^ (k + 1) * Real.exp (-(η * v))) +
        2 * CH * M * ∑ v ∈ Ico v0 V, ((((v : ℝ) + 1) ^ (k + 1) * Real.exp (-(η * v))) *
          (((v : ℝ) + 1) * Real.exp (-((v : ℝ) / 2)))) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ _ := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hS hA2
        · apply mul_le_mul_of_nonneg_left _ hC2
          calc _ ≤ ∑ v ∈ Ico v0 V, (Real.exp 1 * (((k : ℝ) + 1) * k.factorial) / η ^ (k + 1)) *
                (((v : ℝ) + 1) * Real.exp (-((v : ℝ) / 2))) := by
                apply Finset.sum_le_sum
                intro v _
                exact mul_le_mul_of_nonneg_right (hw v) (by positivity)
            _ = (Real.exp 1 * (((k : ℝ) + 1) * k.factorial) / η ^ (k + 1)) *
                ∑ v ∈ Ico v0 V, (((v : ℝ) + 1) * Real.exp (-((v : ℝ) / 2))) := by
                rw [← Finset.mul_sum]
            _ ≤ _ := mul_le_mul_of_nonneg_left hE hK
end Formalism.HermitianLattices.Ext.PrimesInProgressions
