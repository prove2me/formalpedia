-- Prove2me | solution 1 for D1Bound5.finitePPairCoeff_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:21:55.557409+00:00
-- url     : https://prove2.me/submissions/c82121f6-12ad-4a7d-8eee-e2902ddea948

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
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FinitePMatrix_Definitions
import Definitions.Def_D1Bound5_FinitePResidualIdentity_Definitions
import Definitions.Def_D1Bound5_FinitePTailCoefficients_Definitions
import Theorems.Thm_D1Bound5_finitePTailCoeffTerms_admissible
import Theorems.Thm_D1Bound5_finiteP_monomial_bound

section
namespace D1Bound5

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three









theorem finitePPairCoeff_eq_terms (u v : ℂ) (kind side : Fin 2) (l : Fin 3) :
    finitePPairCoeff u v kind side l =
      ∑ t : Fin 3, ((finitePTailCoeffTerms kind side l t).1 : ℂ)*
        (![u,v] side)^(finitePTailCoeffTerms kind side l t).2.1*
        (![v,u] side)^(finitePTailCoeffTerms kind side l t).2.2 := by
  fin_cases kind <;> fin_cases side <;> fin_cases l <;>
    simp [finitePPairCoeff,finitePRLeftCoeff,finitePRRightCoeff,
      finitePTLeftCoeff,finitePTRightCoeff,finitePTailCoeffTerms,Fin.sum_univ_succ] <;> ring

/-- Coefficient-height control with the exact reciprocal-anchor power
needed by its Taylor remainder, proved term by term from integer data. -/
theorem _root_.solution (u v : ℂ) (A S : ℝ)
    (hA1 : 1 ≤ A) (hAu : A ≤ ‖u‖) (hAv : A ≤ ‖v‖)
    (huS : ‖u‖ ≤ S) (hvS : ‖v‖ ≤ S)
    (kind side : Fin 2) (l : Fin 3) :
    ‖finitePPairCoeff u v kind side l‖ ≤
      (finitePTailCoeffWeight kind side l : ℝ)*(S^2/A^4)*
        ‖![u,v] side‖^(5+(l : ℕ)) := by
  let U := ‖![u,v] side‖
  let V := ‖![v,u] side‖
  have hAU : A ≤ U := by fin_cases side <;> assumption
  have hAV : A ≤ V := by fin_cases side <;> assumption
  have hUS : U ≤ S := by fin_cases side <;> assumption
  have hVS : V ≤ S := by fin_cases side <;> assumption
  have hU : 0 < U := by linarith only [hA1,hAU]
  have ht (t : Fin 3) :
      ‖((finitePTailCoeffTerms kind side l t).1 : ℂ)*
        (![u,v] side)^(finitePTailCoeffTerms kind side l t).2.1*
        (![v,u] side)^(finitePTailCoeffTerms kind side l t).2.2‖ ≤
      ((finitePTailCoeffTerms kind side l t).1.natAbs : ℝ)*
        (S^2/A^4)*U^(5+(l : ℕ)) := by
    let m := finitePTailCoeffTerms kind side l t
    have hadm := finitePTailCoeffTerms_admissible kind side l t
    have hq := finiteP_monomial_bound A S U V 4 (5+(l : ℕ)) m.2.1 m.2.2
      hA1 hAU hAV hUS hVS hadm.1 (by dsimp [m]; omega)
    have hm := (div_le_iff₀ (pow_pos hU _)).mp hq
    have hn : ‖(m.1 : ℂ)‖ = (m.1.natAbs : ℝ) := by simp
    change ‖(m.1 : ℂ)*(![u,v] side)^m.2.1*(![v,u] side)^m.2.2‖ ≤ _
    simp only [norm_mul,norm_pow,hn]
    have hh := mul_le_mul_of_nonneg_left hm (show 0 ≤ (m.1.natAbs : ℝ) by positivity)
    simpa only [U, V, mul_assoc] using hh
  rw [finitePPairCoeff_eq_terms]
  calc
    _ ≤ ∑ t : Fin 3, ‖((finitePTailCoeffTerms kind side l t).1 : ℂ)*
        (![u,v] side)^(finitePTailCoeffTerms kind side l t).2.1*
        (![v,u] side)^(finitePTailCoeffTerms kind side l t).2.2‖ := norm_sum_le _ _
    _ ≤ ∑ t : Fin 3, ((finitePTailCoeffTerms kind side l t).1.natAbs : ℝ)*
        (S^2/A^4)*U^(5+(l : ℕ)) := Finset.sum_le_sum (fun t _ => ht t)
    _ = _ := by simp [finitePTailCoeffWeight,Finset.sum_mul,Nat.cast_sum,U]

end D1Bound5
end
