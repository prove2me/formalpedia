-- Prove2me | solution 1 for Formalism.CountingSumsFrames.divPow_sum_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:51:40.301232+00:00
-- url     : https://prove2.me/submissions/d93960b1-6eae-4bc0-946e-7b852c5555b5

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Theorems.Thm_Formalism_CountingSumsFrames_divPow_add_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.CountingSumsFrames
variable {K E : Type*} [Field K] [CharZero K] [Ring E] [Algebra K E]
namespace Formalism.CountingSumsFrames
theorem _root_.solution {ι : Type*} (S : Subsemiring E) (s : Finset ι) (a : ι → E)
    (hc : ∀ i j, Commute (a i) (a j)) (ha : ∀ (i : ι) (n : ℕ), ((n.factorial : K)⁻¹) • a i ^ n ∈ S) :
    ∀ n : ℕ, ((n.factorial : K)⁻¹) • (∑ i ∈ s, a i) ^ n ∈ S := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · simp [zero_pow hn.ne']
  | insert i s hi ih =>
    intro n
    rw [Finset.sum_insert hi]
    exact divPow_add_mem S _ _ (Commute.sum_right _ _ _ fun j _ => hc i j) (ha i) ih n
end Formalism.CountingSumsFrames
