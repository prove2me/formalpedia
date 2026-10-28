-- Prove2me | solution 1 for D1Bound5.finitePRootCoeff_adaptive_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:34:36.596934+00:00
-- url     : https://prove2.me/submissions/81724457-0fef-4f50-873d-446cd9b13525

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FinitePAdaptiveTailBound_Definitions
import Definitions.Def_D1Bound5_FinitePAdaptiveTailData_Definitions
import Definitions.Def_D1Bound5_FinitePHeight_Definitions
import Theorems.Thm_D1Bound5_finitePAdaptiveTailExponent_certificate
import Theorems.Thm_D1Bound5_finiteP_ratio_monomial_bound

section
namespace D1Bound5



theorem _root_.solution (a b s : ℂ)
    (hA : 1 ≤ ‖a‖) (hAB : ‖a‖ ≤ ‖b‖) (hBS : ‖b‖ ≤ ‖s‖)
    (i : Fin 4) (l j : Fin 3) :
    ‖finitePRootCoeff a b s i l j‖ ≤
      finitePAdaptiveTailCoeffWeight i l j (‖a‖/‖b‖)*
        (‖s‖^2/‖a‖^4)*‖![a,b,s] j‖^(5+(l : ℕ)) := by
  let A := ‖a‖
  let B := ‖b‖
  let S := ‖s‖
  let U := ‖![a,b,s] j‖
  have hA0 : 0 < A := by linarith only [hA]
  have hB0 : 0 < B := hA0.trans_le hAB
  have hS0 : 0 < S := hB0.trans_le hBS
  have hAU : A ≤ U := by
    fin_cases j
    · exact le_rfl
    · exact hAB
    · exact hAB.trans hBS
  have hU : 0 < U := hA0.trans_le hAU
  have hroot : ![A,B,S] j = U := by fin_cases j <;> rfl
  have ht (t : Fin 3) : ‖finitePTermValue (finitePRootTerms i l j t) a b s‖ ≤
      |((finitePRootTerms i l j t).1 : ℝ)| *(A/B)^(finitePAdaptiveTailExponent i l j t)*
        (S^2/A^4)*U^(5+(l : ℕ)) := by
    let u := finitePRootTerms i l j t
    let e := finitePAdaptiveTailExponent i l j t
    obtain ⟨hdeg,h0,h1,h2⟩ := finitePAdaptiveTailExponent_certificate i l j t
    have he : e+u.2.2.1+u.2.2.2 = if j=0 then 2 else (4+(l : ℕ))+2 := by
      fin_cases j
      · exact h0 rfl
      · exact (h1 rfl).1
      · exact h2 rfl
    have hl : j ≠ 2 → u.2.2.2 ≤ 2 := by
      intro hj
      fin_cases j
      · have hh := h0 rfl
        dsimp [u] at *
        omega
      · exact (h1 rfl).2
      · exact False.elim (hj rfl)
    have hr := finiteP_ratio_monomial_bound A B S hA hAB hBS j
      u.2.1 u.2.2.1 u.2.2.2 (4+(l : ℕ)) 3 e hdeg he hl
    rw [hroot] at hr
    have hm := (div_le_iff₀ (pow_pos hU _)).mp hr
    have hextra : (S^2/A^3)*(A/B)^e*U^(4+(l : ℕ)) ≤
        (A/B)^e*(S^2/A^4)*U^(5+(l : ℕ)) := by
      have hh := mul_le_mul_of_nonneg_left hAU
        (show 0 ≤ S^2*(A/B)^e*U^(4+(l : ℕ))/A^4 by positivity)
      calc
        _ = (S^2*(A/B)^e*U^(4+(l : ℕ))/A^4)*A := by
          field_simp [hA0.ne'] <;> ring
        _ ≤ (S^2*(A/B)^e*U^(4+(l : ℕ))/A^4)*U := hh
        _ = _ := by
          simp only [show 5+(l : ℕ)=(4+(l : ℕ))+1 by omega,pow_add,pow_one]
          ring
    have hscalar := hm.trans hextra
    have hnorm : ‖(u.1 : ℂ)‖ = |(u.1 : ℝ)| := by simp
    have hh := mul_le_mul_of_nonneg_left hscalar (abs_nonneg (u.1 : ℝ))
    simpa [finitePTermValue,norm_mul,norm_pow,hnorm,A,B,S,U,u,e,mul_assoc] using hh
  calc
    _ ≤ ∑ t, ‖finitePTermValue (finitePRootTerms i l j t) a b s‖ := norm_sum_le _ _
    _ ≤ ∑ t, |((finitePRootTerms i l j t).1 : ℝ)| *
        (A/B)^(finitePAdaptiveTailExponent i l j t)*(S^2/A^4)*U^(5+(l : ℕ)) :=
      Finset.sum_le_sum (fun t _ => ht t)
    _ = _ := by simp [finitePAdaptiveTailCoeffWeight,Finset.sum_mul,A,B,S,U]





end D1Bound5
end
