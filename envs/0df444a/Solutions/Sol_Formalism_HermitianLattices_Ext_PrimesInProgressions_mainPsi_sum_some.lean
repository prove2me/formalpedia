-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.mainPsi_sum_some
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:37:21.779621+00:00
-- url     : https://prove2.me/submissions/6ed8b0fd-e1a8-4240-b63e-6cf296f49942

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTEOf
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTPiB
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SiegelWalfiszAPOf
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_ExcTerm
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTPiA

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
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet ArithmeticFunction
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution (M : ℕ) [NeZero M] (b : ℕ) (hb : b.Coprime M) (χ₁ : DirichletCharacter ℂ M)
    (β t : ℝ) (ht : 0 ≤ t) (hχ : χ₁ (b : ZMod M) = 1 ∨ χ₁ (b : ZMod M) = -1) :
    ∑ χ : DirichletCharacter ℂ M, χ ((b : ZMod M)⁻¹) * mainPsi (some (χ₁, β)) χ t =
      ((t - (χ₁ (b : ZMod M)).re * t ^ β / β : ℝ) : ℂ) := by
  have hbu : (b : ZMod M) * (b : ZMod M)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one b hb
  have hunit : IsUnit ((b : ZMod M)⁻¹) :=
    ⟨⟨(b : ZMod M)⁻¹, (b : ZMod M), by rw [mul_comm]; exact hbu, hbu⟩, rfl⟩
  have h1 : (1 : DirichletCharacter ℂ M) ((b : ZMod M)⁻¹) = 1 := MulChar.one_apply hunit
  have h2 : χ₁ ((b : ZMod M)⁻¹) = χ₁ (b : ZMod M) := by
    have h3 := congrArg χ₁ hbu
    rw [map_mul, map_one] at h3
    rcases hχ with h | h
    · rw [h, one_mul] at h3
      rw [h3, h]
    · rw [h] at h3 ⊢
      linear_combination -h3
  have hre : ((χ₁ (b : ZMod M)).re : ℂ) = χ₁ (b : ZMod M) := by
    rcases hχ with h | h <;> simp [h]
  simp only [mainPsi, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, h1, h2]
  push_cast
  rw [hre, Complex.ofReal_cpow ht]
  ring
end Formalism.HermitianLattices.Ext.PrimesInProgressions
