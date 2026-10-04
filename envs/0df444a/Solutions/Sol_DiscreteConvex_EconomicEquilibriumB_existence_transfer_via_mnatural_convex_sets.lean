-- Prove2me | solution 1 for DiscreteConvex.EconomicEquilibriumB.existence_transfer_via_mnatural_convex_sets
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T19:27:41.943989+00:00
-- url     : https://prove2.me/submissions/0132484d-df40-49c8-901c-103f6b0ce4e0

import Mathlib
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_DemandSet
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_SupplySet
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_IsEquilibrium
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_IsMNaturalConvexSet
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_IsContEquilibrium

set_option autoImplicit false
set_option linter.unusedVariables false

open DiscreteConvex.EconomicEquilibriumB

namespace ETCex

/-- A utility with no affine majorant: `U(y) = y²`. -/
def U0 : Unit → (Unit → ℤ) → WithBot ℝ := fun _ y => (((y () : ℝ) ^ 2 : ℝ) : WithBot ℝ)

/-- A large integer beats any affine bound. -/
theorem big (a b : ℝ) : ∃ n : ℤ, a + b * n < (n : ℝ) ^ 2 := by
  obtain ⟨n, hn⟩ := exists_nat_gt (|a| + |b| + 1)
  refine ⟨n, ?_⟩
  push_cast
  have h1 := le_abs_self a
  have h2 := le_abs_self b
  have h3 := abs_nonneg a
  have h4 := abs_nonneg b
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have e1 : b * n ≤ |b| * n := mul_le_mul_of_nonneg_right h2 (by linarith)
  have e2 : |a| ≤ |a| * n := by nlinarith
  have e3 : (|a| + |b| + 1) * n < (n : ℝ) * n := mul_lt_mul_of_pos_right hn (by linarith)
  nlinarith

theorem closure_top (z : Unit → ℝ) : ConcaveClosureR (U0 ()) z = ⊤ := by
  unfold ConcaveClosureR
  rw [← sInf_empty (α := EReal)]
  congr 1
  refine Set.eq_empty_iff_forall_notMem.mpr ?_
  rintro v ⟨p, α, hmaj, -⟩
  obtain ⟨n, hn⟩ := big α (p ())
  have := hmaj (fun _ => n)
  rw [show ToERealOfBot (U0 () (fun _ => n)) = ((((n : ℤ) : ℝ) ^ 2 : ℝ) : EReal) from rfl] at this
  simp only [Finset.univ_unique, Finset.sum_singleton] at this
  have h' : (((n : ℤ) : ℝ) ^ 2) ≤ α + p () * n := by exact_mod_cast this
  linarith

theorem demand_empty (p : Unit → ℝ) : DemandSet (U0 ()) p = ∅ := by
  ext x
  simp only [DemandSet, ArgMaxBot, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  intro hx
  obtain ⟨n, hn⟩ := big ((x () : ℝ) ^ 2 - p () * x ()) (p ())
  have := hx (fun _ => n)
  simp only [PriceShift, U0, Finset.univ_unique, Finset.sum_singleton] at this
  rw [← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_le_coe] at this
  linarith

theorem cont_demand (p x : Unit → ℝ) : x ∈ ContDemandSet (U0 ()) p := by
  intro z
  rw [closure_top, closure_top, EReal.top_add_coe, EReal.top_add_coe]

end ETCex

theorem solution : ¬ (∀ {K : Type} [Fintype K] [DecidableEq K] {H L : Type} [Fintype H] [Fintype L]
    (U : H → (K → ℤ) → WithBot ℝ) (C : L → (K → ℤ) → WithTop ℝ)
    (hD : ∀ p : K → ℝ, (∀ k, 0 ≤ p k) → ∀ h, (DemandSet (U h) p).Nonempty →
      IsMNaturalConvexSet (DemandSet (U h) p))
    (hS : ∀ p : K → ℝ, (∀ k, 0 ≤ p k) → ∀ l, (SupplySet (C l) p).Nonempty →
      IsMNaturalConvexSet (SupplySet (C l) p))
    (x0 : K → ℤ) (hx0 : ∀ k, 0 ≤ x0 k) (xc : H → (K → ℝ)) (yc : L → (K → ℝ)) (pc : K → ℝ)
    (hcont : IsContEquilibrium U C x0 xc yc pc),
    ∃ (x : H → (K → ℤ)) (y : L → (K → ℤ)) (p : K → ℝ), IsEquilibrium U C x0 x y p) := by
  intro h
  obtain ⟨x, y, p, hd, -⟩ := h (K := Unit) (H := Unit) (L := Empty) ETCex.U0 (fun l => l.elim)
    (fun p _ h hne => by rw [ETCex.demand_empty] at hne; exact absurd hne Set.not_nonempty_empty)
    (fun p _ l => l.elim) (fun _ => 0) (fun _ => le_rfl) (fun _ _ => 0) (fun l => l.elim)
    (fun _ => 0)
    ⟨fun h => ETCex.cont_demand _ _, fun l => l.elim, by funext k; simp, fun _ => le_rfl⟩
  have := hd ()
  rw [ETCex.demand_empty] at this
  exact this

#print axioms solution
