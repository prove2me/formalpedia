-- Prove2me | solution 1 for Formalism.CountingSumsFrames.pow_log_smul_harmonicProj_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:50:26.043471+00:00
-- url     : https://prove2.me/submissions/7e1f223f-ca63-41fd-8ef5-8e9ad2000cea

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Theorems.Thm_Formalism_CountingSumsFrames_pow_log_div_choose_mem

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
variable {K : Type} [Field K] [CharZero K] {k : ℕ}
namespace Formalism.CountingSumsFrames
theorem _root_.solution (R : Subring K) (p : ℕ) (hp : p.Prime) (hR : PLocal R p) (M : Set (PolXY K k))
    (h0 : (0 : PolXY K k) ∈ M) (hadd : ∀ f g, f ∈ M → g ∈ M → f + g ∈ M)
    (hs : ∀ r ∈ R, ∀ f ∈ M, r • f ∈ M)
    (hM : ∀ (l : ℕ) (f : PolXY K k), f ∈ M → hDiv K k l f ∈ M ∧ ctrDiv K k l f ∈ M)
    (a b N : ℕ) (hN : a + b + k ≤ N) (f : PolXY K k) (hf : f ∈ M) :
    ((p : K) ^ Nat.log p N) • harProj K k a b f ∈ M := by
  have hsum : ∀ (s : Finset ℕ) (F : ℕ → PolXY K k), (∀ l ∈ s, F l ∈ M) → ∑ l ∈ s, F l ∈ M := by
    classical
    intro s F
    induction s using Finset.induction_on with
    | empty => intro _; simpa using h0
    | insert i s hi ih =>
      intro h
      rw [Finset.sum_insert hi]
      exact hadd _ _ (h i (Finset.mem_insert_self i s)) (ih fun l hl => h l (Finset.mem_insert_of_mem hl))
  rw [harProj, LinearMap.sum_apply, Finset.smul_sum]
  refine hsum _ _ fun l _ => ?_
  rw [LinearMap.smul_apply, LinearMap.comp_apply, smul_smul]
  refine hs _ ?_ _ (hM l _ (hM l f hf).2).1
  have : (p : K) ^ Nat.log p N * ((-1 : K) ^ l / (((a + b + k - 2).choose l : ℕ) : K)) =
      (-1 : K) ^ l * ((p : K) ^ Nat.log p N / (((a + b + k - 2).choose l : ℕ) : K)) := by ring
  rw [this]
  exact R.mul_mem (R.pow_mem (R.neg_mem R.one_mem) l) (pow_log_div_choose_mem R p hp hR _ N l (by omega))
end Formalism.CountingSumsFrames
