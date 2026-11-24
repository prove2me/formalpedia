-- Prove2me | solution 1 for Formalism.HermitianLattices.RamifiedHeckeModels.cauchy_schwarz_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:46:58.680795+00:00
-- url     : https://prove2.me/submissions/d48291f2-ba09-43b9-85f9-d0fb4e254316

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_RationalMatrixPrimeOrderBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_FourierCommutesHeckeScalar
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_LengthQuotientLeOfLatticeSandwich
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_LengthQuotientBoundGeneral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.RamifiedHeckeModels
open Formalism.HermitianLattices.LocalLatticeBases Finset ComplexConjugate
namespace Formalism.HermitianLattices.RamifiedHeckeModels
theorem _root_.solution : CauchySchwarzUnitModulus := by
  intro V _ _ y y' T ε hT hy hy'
  have he : ‖y'‖ = ‖y‖ :=
    (pow_left_inj₀ (norm_nonneg y') (norm_nonneg y) two_ne_zero).1 (hy'.trans hy.symm)
  refine ⟨?_, ?_⟩
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hT.le]
    calc T * ‖inner ℂ y y'‖ ≤ T * (‖y‖ * ‖y'‖) :=
          mul_le_mul_of_nonneg_left (norm_inner_le_norm y y') hT.le
      _ = 1 := by rw [he, ← sq, hy]; field_simp
  · intro hε h
    have hT0 : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'

    rcases hε with rfl | rfl
    · have hi : inner ℂ y y' = ((1 / T : ℝ) : ℂ) := by
        push_cast; field_simp; rw [mul_comm]; exact h
      have hi' : inner ℂ y' y = ((1 / T : ℝ) : ℂ) := by
        rw [← inner_conj_symm, hi, Complex.conj_ofReal]
      have h0 : ‖y' - y‖ ^ 2 = 0 := by
        rw [@norm_sub_sq ℂ, hi', hy, hy']
        simp only [RCLike.re_to_complex, Complex.ofReal_re]
        ring
      rw [one_smul]
      exact sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h0))
    · have hi : inner ℂ y y' = ((-(1 / T) : ℝ) : ℂ) := by
        push_cast; field_simp; rw [mul_comm]; exact h
      have hi' : inner ℂ y' y = ((-(1 / T) : ℝ) : ℂ) := by
        rw [← inner_conj_symm, hi, Complex.conj_ofReal]
      have h0 : ‖y' + y‖ ^ 2 = 0 := by
        rw [@norm_add_sq ℂ, hi', hy, hy']
        simp only [RCLike.re_to_complex, Complex.ofReal_re]
        ring
      rw [neg_one_smul, ← sub_eq_zero, sub_neg_eq_add]
      exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h0)
end Formalism.HermitianLattices.RamifiedHeckeModels
