-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.coeff_mvExp_linF_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:37:27.48919+00:00
-- url     : https://prove2.me/submissions/f689695a-ef22-454b-996e-b8bedbd3760c

import Mathlib
import Definitions.Def_Formalism_IncomingBounds_StatementThmP
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ThmPExp
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_Cayley
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_MfactMulCoeffMvExpLinF
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_linF_pow_step
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
open MvPowerSeries
namespace Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
section ExpLin
variable {K : Type} [Field K] {τ : Type} [Fintype τ]
variable [CharZero K]
private theorem coeff_mvExp_eq_sum_range_degree {K : Type} [Field K] {ρ : Type} (h : MvPowerSeries ρ K) (m : ρ →₀ ℕ) :
    coeff m (Formalism.IncomingBounds.mvExp h) = ∑ k ∈ Finset.range (m.degree + 1), coeff m (h ^ k) / (k.factorial : K) := rfl
private theorem add_single_one_ne_zero {ρ : Type} (m : ρ →₀ ℕ) (w : ρ) : m + Finsupp.single w 1 ≠ 0 := by
  intro h
  have := congrArg (fun f : ρ →₀ ℕ => f w) h
  simp at this
end ExpLin
section Rename
variable {K : Type} [Field K] {σ τ : Type}
end Rename
end Formalism.L2.FormalSeriesBounds
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MvPowerSeries
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
variable {K : Type} [Field K] {τ : Type} [Fintype τ]
variable [CharZero K]
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (lam : τ → K) (w : τ) (m : τ →₀ ℕ) :
    coeff (m + Finsupp.single w 1) (mvExp (linF lam)) * ((m w : K) + 1)
      = lam w * coeff m (mvExp (linF lam)) := by
  rw [coeff_mvExp_eq_sum_range_degree, coeff_mvExp_eq_sum_range_degree, map_add Finsupp.degree, Finsupp.degree_single,
    Finset.sum_range_succ', Finset.mul_sum, add_mul, Finset.sum_mul]
  have h0 : coeff (m + Finsupp.single w 1) (linF lam ^ 0) = 0 := by
    classical
    rw [pow_zero, MvPowerSeries.coeff_one, if_neg (add_single_one_ne_zero m w)]
  rw [h0, zero_div, zero_mul, add_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h3 := coeff_linF_pow_step lam w m j
  have hf : (j.factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hj : ((j : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
  rw [div_mul_eq_mul_div, h3, Nat.factorial_succ, Nat.cast_mul]
  push_cast
  field_simp
end Formalism.L2.FormalSeriesBounds
