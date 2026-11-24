-- Prove2me | solution 1 for BSLambda.LLL.pr_le_pow_of_pinned
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:25:57.376428+00:00
-- url     : https://prove2.me/submissions/ad72f8aa-ce8a-4367-ae6f-3859c7be7353

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Prob
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Asymmetric
public import Theorems.Thm_BSLambda_LLL_pr_le_prod_of_pinned

set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.LLL
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {β : A → Type*} [∀ a, Fintype (β a)] [∀ a, DecidableEq (β a)] [∀ a, Nonempty (β a)]
variable {I : Type*} [Fintype I] [DecidableEq I]
omit [∀ a, DecidableEq (β a)]
namespace BSLambda.LLL
theorem _root_.solution {G T : Finset A} (hGT : Disjoint G T) (N : ℕ)
    (hN : ∀ a ∈ T, Fintype.card (β a) = N)
    (tgt : ((a : A) → a ∈ G → β a) → (a : A) → Finset (β a)) (m : ℕ)
    (hm : ∀ c, ∀ a ∈ T, (tgt c a).card ≤ m) {E : Finset (Cfg β)}
    (hE : ∀ ω ∈ E, ∀ a ∈ T, ω a ∈ tgt (fun b _ ↦ ω b) a) :
    pr E ≤ ((m : ℝ) / N) ^ T.card := by
  classical
  exact
  (pr_le_prod_of_pinned hGT tgt m hm hE).trans_eq <|
    (Finset.prod_congr rfl fun a ha ↦ by rw [hN a ha]).trans (Finset.prod_const _)
end BSLambda.LLL
