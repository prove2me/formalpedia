-- Prove2me | solution 1 for Formalism.HermitianLattices.IntegralLatticeDensity.weber_function_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:04:51.911836+00:00
-- url     : https://prove2.me/submissions/c265d63e-c2f5-4025-9e94-3438228962dc

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_InvariantSeriesBidegreeOneOne
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_FourFoldOrthogonalSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.IntegralLatticeDensity
open Finset
namespace Formalism.HermitianLattices.IntegralLatticeDensity
theorem _root_.solution : WeberRoot := by
  intro x j s hs hj hx
  have hs0 : (s : ℂ) ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
  refine ⟨?_, ?_⟩
  · let R := integralClosure ℤ ℂ
    let jR : R := ⟨j, hj⟩
    let q : Polynomial R := (Polynomial.X - Polynomial.C (s : R)) ^ 3 - Polynomial.C jR * Polynomial.X
    have hq : q.Monic := by
      apply Polynomial.Monic.sub_of_left ((Polynomial.monic_X_sub_C _).pow 3)
      rw [Polynomial.degree_pow, Polynomial.degree_X_sub_C]
      refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_le _) ?_
      norm_num
    have hxR : IsIntegral R x := by
      refine ⟨q, hq, ?_⟩
      simp only [q, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_C, Polynomial.eval₂_mul]
      simp only [map_intCast]
      have hjR : algebraMap R ℂ jR = j := rfl
      rw [hjR]
      linear_combination hx
    exact isIntegral_trans x hxR
  · intro h
    rw [h] at hx
    apply hs0
    have h3 : (s : ℂ) ^ 3 = 0 := by linear_combination -hx
    exact (pow_eq_zero_iff (by norm_num)).mp h3
end Formalism.HermitianLattices.IntegralLatticeDensity
