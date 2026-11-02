-- Prove2me | solution 1 for DynRiskEq.Welfare.theorem_3_i
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T06:42:49.448932+00:00
-- url     : https://prove2.me/submissions/9248f2c4-74b4-472a-8fb4-83df7bb90ce3

import Mathlib
import Definitions.Def_DynRiskEq_Welfare_Model

open StochasticProg.Multistage FirstOrderOpt.ConvexTheory
open scoped RealInnerProductSpace

namespace DynRiskEq.Welfare.Aux3

open DynRiskEq.Welfare

variable {H : ℕ} (T : Tree H) {A : Type} [Fintype A] [DecidableEq A]

lemma t3i (M : Market T A) (Ka : A → T.Node → ℕ)
    (pa : (a : A) → (n : T.Node) → Fin (Ka a n) → T.Node → ℝ)
    (π : T.Node → ℝ) (α : (a : A) → T.Node → Vec (M.dX a)) (μ : T.Node → ℝ)
    (u : (a : A) → T.Node → Vec (M.dU a)) (x : (a : A) → T.Node → Vec (M.dX a))
    (W : A → T.Node → ℝ) (θa : A → T.Node → ℝ)
    (hRTE : IsRTE T M Ka pa π α μ u x W θa) :
    ∀ n, ¬ IsLeaf T n →
      (∀ a, InRisk T (Ka a) (pa a) n μ) ∧ restrictChildren T μ n ∈ socialRiskSet T Ka pa n := by
  intro n hn
  have hall : ∀ a, InRisk T (Ka a) (pa a) n μ := by
    intro a
    obtain ⟨γ, h20a, h20b, -, -, -, -, h20g⟩ := hRTE.1 a
    have heq : restrictChildren T μ n =
        ∑ k, γ n k • restrictChildren T (pa a n k) n := by
      funext m
      simp only [restrictChildren, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      linarith [h20g n hn m m.2]
    unfold InRisk riskSet
    rw [heq]
    refine (convex_convexHull ℝ _).sum_mem (fun k _ => (h20b n hn k).1) ?_
      (fun k _ => subset_convexHull ℝ _ ⟨k, rfl⟩)
    linarith [h20a n hn]
  exact ⟨hall, Set.mem_iInter.2 hall⟩

end DynRiskEq.Welfare.Aux3

open DynRiskEq.Welfare DynRiskEq.Welfare.Aux3

theorem solution {H : ℕ} (T : Tree H) {A : Type} [Fintype A] [DecidableEq A]
    (M : Market T A) (Ka : A → T.Node → ℕ)
    (pa : (a : A) → (n : T.Node) → Fin (Ka a n) → T.Node → ℝ)
    (π : T.Node → ℝ) (α : (a : A) → T.Node → Vec (M.dX a)) (μ : T.Node → ℝ)
    (u : (a : A) → T.Node → Vec (M.dU a)) (x : (a : A) → T.Node → Vec (M.dX a))
    (W : A → T.Node → ℝ) (θa : A → T.Node → ℝ)
    (hRTE : IsRTE T M Ka pa π α μ u x W θa) :
    ∀ n, ¬ IsLeaf T n →
      (∀ a, InRisk T (Ka a) (pa a) n μ) ∧ restrictChildren T μ n ∈ socialRiskSet T Ka pa n := by
  exact t3i T M Ka pa π α μ u x W θa hRTE
