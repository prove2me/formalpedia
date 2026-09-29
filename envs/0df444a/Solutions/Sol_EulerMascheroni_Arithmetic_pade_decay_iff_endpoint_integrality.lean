-- Prove2me | solution 1 for EulerMascheroni.Arithmetic.pade_decay_iff_endpoint_integrality
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T15:15:25.614353+00:00
-- url     : https://prove2.me/submissions/e13a8c20-3952-4c01-92c9-93e71b331417

import Definitions.Def_eulerMascheroni_padeDecay
import Theorems.Thm_EulerMascheroni_Arithmetic_quotient_coefficient_properties
open EulerMascheroni.Arithmetic
namespace EulerEndpoint
lemma integral_prefix_iff (a : ℝ) (D n : ℕ) :
    (∀ k : ℕ, k ≤ n → IsIntegral ℤ ((D:ℝ)*quotientCoeff a k)) ↔
      IsIntegral ℤ ((D:ℝ)*quotientCoeff a n) := by
  constructor
  · intro h
    exact h n le_rfl
  · intro h
    induction n with
    | zero =>
      intro k hk
      have he : k=0 := by omega
      simpa [he] using h
    | succ n ih =>
      have hn : IsIntegral ℤ ((D:ℝ)*quotientCoeff a n) := by
        have hrec := ((quotient_coefficient_properties a).2 n).1
        have hi := ((isIntegral_natCast (n+1) : IsIntegral ℤ ((n+1:ℕ):ℝ)).mul h).add
          ((isIntegral_natCast D : IsIntegral ℤ (D:ℝ)).mul
            ((isIntegral_one : IsIntegral ℤ (1:ℝ)).neg.pow n))
        have heq : (D:ℝ)*quotientCoeff a n =
            ((n+1:ℕ):ℝ)*((D:ℝ)*quotientCoeff a (n+1))+(D:ℝ)*(-1:ℝ)^n := by
          linear_combination -(D:ℝ)*hrec
        rw [heq]
        exact hi
      intro k hk
      by_cases he : k=n+1
      · simpa [he] using h
      · exact ih hn k (by omega)
lemma decay_iff_endpoint (a : ℝ) :
    PadeDecayDenominators a ↔
    ∃ D : ℕ → ℕ, (∀ n, 0 < D n) ∧
      Filter.Tendsto (fun n => (D n:ℝ)*4^n/(n.factorial:ℝ)) Filter.atTop (nhds 0) ∧
      ∀ n, IsIntegral ℤ ((D n:ℝ)*quotientCoeff a (2*n)) := by
  constructor
  · rintro ⟨D,hpos,hlim,hi⟩
    exact ⟨D,hpos,hlim,fun n => hi n (2*n) le_rfl⟩
  · rintro ⟨D,hpos,hlim,hi⟩
    exact ⟨D,hpos,hlim,fun n => (integral_prefix_iff a (D n) (2*n)).mpr (hi n)⟩
end EulerEndpoint


theorem solution (a : ℝ) :
    PadeDecayDenominators a ↔
    ∃ D : ℕ → ℕ, (∀ n, 0 < D n) ∧
      Filter.Tendsto (fun n => (D n:ℝ)*4^n/(n.factorial:ℝ)) Filter.atTop (nhds 0) ∧
      ∀ n, IsIntegral ℤ ((D n:ℝ)*quotientCoeff a (2*n)) := by
  exact EulerEndpoint.decay_iff_endpoint a

#print axioms solution
