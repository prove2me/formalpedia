-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.dhpr_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:16:55.218988+00:00
-- url     : https://prove2.me/submissions/35007dff-ed92-4b53-a4cd-02ceaf9c7c51

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHPos
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_DHFinish2Of
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LDerivNearOne
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHPrimeA
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_dhPos_hasSum


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
open scoped LSeries.notation ComplexOrder
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution {M : ℕ} [NeZero M] (χ₁ : DirichletCharacter ℂ M) (k : ℕ) {σ : ℝ}
    (hσ : 1 < σ) :
    HasSum (fun n : ℕ => (Real.log n) ^ k * (Λ n / (n : ℝ) ^ σ) * dhprC χ₁ n)
      ((-1 : ℂ) ^ k * (iteratedDeriv k (negLD (1 : DirichletCharacter ℂ M)) (σ : ℂ)
        + iteratedDeriv k (negLD χ₁) (σ : ℂ))).re := by
  have hs : 1 < ((σ : ℂ)).re := by simpa using hσ
  have h1 := dhPos_hasSum (1 : DirichletCharacter ℂ M) k hs
  have h2 := dhPos_hasSum χ₁ k hs
  have h3 := h1.add h2
  rw [show ((-1 : ℂ) ^ k * (iteratedDeriv k (negLD (1 : DirichletCharacter ℂ M)) (σ : ℂ)
      + iteratedDeriv k (negLD χ₁) (σ : ℂ))).re =
      ((-1 : ℂ) ^ k * iteratedDeriv k (negLD (1 : DirichletCharacter ℂ M)) (σ : ℂ)).re +
      ((-1 : ℂ) ^ k * iteratedDeriv k (negLD χ₁) (σ : ℂ)).re by rw [mul_add, Complex.add_re]]
  convert h3 using 1
  funext n
  have hiter : ∀ (f : ℕ → ℂ) (j m : ℕ), (LSeries.logMul^[j] f) m = (Complex.log m) ^ j * f m := by
    intro f j
    induction j with
    | zero => intro m; simp
    | succ j ih =>
      intro m
      rw [Function.iterate_succ_apply', LSeries.logMul, ih]
      ring
  by_cases hn : n = 0
  · subst hn
    simp [LSeries.term]
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, hiter, hiter]
  simp only [Pi.mul_apply]
  have hn' : (n : ℂ) = ((n : ℝ) : ℂ) := by push_cast; rfl
  rw [hn', ← Complex.ofReal_log (Nat.cast_nonneg _), ← Complex.ofReal_cpow (Nat.cast_nonneg _), ← Complex.ofReal_pow]
  simp only [Complex.div_ofReal_re, Complex.re_ofReal_mul, Complex.re_mul_ofReal]
  unfold dhprC
  ring
end Formalism.HermitianLattices.Ext.PrimesInProgressions
