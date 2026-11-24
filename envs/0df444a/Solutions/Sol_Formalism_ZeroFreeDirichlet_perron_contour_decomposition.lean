-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.perron_contour_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:45:09.202104+00:00
-- url     : https://prove2.me/submissions/d0993a15-898b-4226-bee9-10f4ba3485e3

import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_PerronHorizontalSegmentBound
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_IntegralEqIntervalIntegralAddCompl
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_NormIntegralComplLe
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_ExistsContourAvoidingRealZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution (hP : PerronChi) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (y σ₁ σ₀ T : ℝ) (R : ℂ) (hy : 1 ≤ y) (hσ₀ : 1 < σ₀) (hT : 0 ≤ T)
    (hrect : Formalism.ZF.rectInt (Fchi χ y) σ₁ σ₀ (-T) T = 2 * Real.pi * I * R) :
    2 * Real.pi * ‖Schi χ y - R‖ ≤
      ‖∫ t in (Set.Ioc (-T) T)ᶜ, Fchi χ y ((σ₀ : ℂ) + t * I)‖
      + ‖∫ x in σ₁..σ₀, Fchi χ y ((x : ℂ) + ((-T : ℝ) : ℂ) * I)‖
      + ‖∫ x in σ₁..σ₀, Fchi χ y ((x : ℂ) + (T : ℂ) * I)‖
      + ‖∫ u in (-T)..T, Fchi χ y ((σ₁ : ℂ) + u * I)‖ := by
  obtain ⟨hint, hS⟩ := hP q χ y hy σ₀ hσ₀
  have hsplit := integral_add_compl (s := Set.Ioc (-T) T) measurableSet_Ioc hint
  have hIoc : ∫ t in Set.Ioc (-T) T, Fchi χ y ((σ₀ : ℂ) + t * I) =
      ∫ t in (-T)..T, Fchi χ y ((σ₀ : ℂ) + t * I) :=
    (intervalIntegral.integral_of_le (by linarith)).symm
  unfold Formalism.ZF.rectInt at hrect
  set Cp := ∫ t in (Set.Ioc (-T) T)ᶜ, Fchi χ y ((σ₀ : ℂ) + t * I) with hCp
  set Bt := ∫ x in σ₁..σ₀, Fchi χ y ((x : ℂ) + ((-T : ℝ) : ℂ) * I) with hBt
  set Tp := ∫ x in σ₁..σ₀, Fchi χ y ((x : ℂ) + (T : ℂ) * I) with hTp
  set Lf := ∫ u in (-T)..T, Fchi χ y ((σ₁ : ℂ) + u * I) with hLf
  set Rt := ∫ t in (-T)..T, Fchi χ y ((σ₀ : ℂ) + t * I) with hRt
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')
  have hinv : (2 * (Real.pi : ℂ)) * (1 / (2 * Real.pi)) = 1 := by field_simp
  have hI : I * I = -1 := Complex.I_mul_I
  have key : (2 * (Real.pi : ℂ)) * (Schi χ y - R) = Cp + I * (Bt - Tp) + Lf := by
    rw [hS, ← hsplit, hIoc]
    linear_combination (-I) * hrect + (Rt + Cp) * hinv + (Rt - Lf - 2 * Real.pi * R) * hI
  have hn : ‖(2 * (Real.pi : ℂ))‖ = 2 * Real.pi := by
    rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_of_nonneg (by positivity)]
  have hsub := norm_sub_le Bt Tp
  calc 2 * Real.pi * ‖Schi χ y - R‖ = ‖(2 * (Real.pi : ℂ)) * (Schi χ y - R)‖ := by
        rw [norm_mul, hn]
    _ = ‖Cp + I * (Bt - Tp) + Lf‖ := by rw [key]
    _ ≤ ‖Cp‖ + ‖I * (Bt - Tp)‖ + ‖Lf‖ := norm_add₃_le
    _ ≤ ‖Cp‖ + ‖Bt‖ + ‖Tp‖ + ‖Lf‖ := by
        rw [norm_mul, Complex.norm_I, one_mul]
        linarith
end Formalism.ZeroFreeDirichlet
