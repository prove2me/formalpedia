-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.NU.card_fib
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:43:11.158813+00:00
-- url     : https://prove2.me/submissions/4e1b9fdf-1954-4f1c-9850-e4f1d1ad0971

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_NormUnitary
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_NU_pow_sum_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open Formalism Formalism.NormUnitaryCountingLemmas Formalism.NormUnitaryCountingLemmas.NU
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
namespace Formalism.NormUnitaryCountingLemmas.NU
theorem _root_.solution {d : ℕ} (e : σ →₀ ℕ) (he : ∑ i, e i = d) :
    (univ.filter fun t : Fin d → σ => cnt t = e).card * fct e = d.factorial := by
  have h := congrArg (coeff e) (pow_sum_X (σ := σ) d)
  rw [Finset.sum_pow_eq_sum_piAntidiag] at h
  have hk : ∀ k : σ → ℕ, (∏ i, (X i : MvPolynomial σ ℕ) ^ k i) =
      monomial (Finsupp.equivFunOnFinite.symm k) 1 := by
    intro k
    rw [Finsupp.equivFunOnFinite_symm_eq_sum, monomial_sum_one]
    simp [X_pow_eq_monomial]
  simp only [hk, coeff_sum, coeff_monomial] at h
  have hc : ∀ k : σ → ℕ, coeff e ((Nat.multinomial univ k : MvPolynomial σ ℕ) *
      monomial (Finsupp.equivFunOnFinite.symm k) 1) =
      if k = ⇑e then Nat.multinomial univ k else 0 := by
    intro k
    rw [← map_natCast (C : ℕ →+* MvPolynomial σ ℕ), C_mul_monomial, mul_one, coeff_monomial]
    by_cases hke : k = ⇑e
    · subst hke; simp
    · rw [if_neg hke, if_neg]
      intro h'; apply hke; rw [← h']; simp
  simp only [hc, Finset.sum_ite_eq', Finset.sum_boole] at h
  rw [if_pos (by simp [he])] at h
  rw [Nat.cast_id] at h
  rw [← h, mul_comm, fct, ← he]
  exact Nat.multinomial_spec _ _
end Formalism.NormUnitaryCountingLemmas.NU
