-- Prove2me | solution 1 for DiscreteConvex.MConvexFunctionsC.shared_convex_combination
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T17:55:21.989013+00:00
-- url     : https://prove2.me/submissions/5ffaaa5a-a10f-412f-94b9-cd765d5cd5a6

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_MNaturalConvex
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_IntegralNeighborhoodFinset
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_ConvexClosureVal

set_option autoImplicit false

open DiscreteConvex.MConvexFunctionsC

namespace SharedCex

noncomputable def topF : (Unit → ℤ) → WithTop ℝ := fun _ => ⊤

theorem topF_mnat : MNaturalConvex topF := by
  intro x hx
  exfalso
  apply hx
  simp [LiftedFunction, topF]

theorem sInf_sub_top {s : Set (WithTop ℝ)} (h : s ⊆ {⊤}) : sInf s = ⊤ := by
  classical
  exact if_pos (Or.inl h)

theorem topF_closure (x : Unit → ℝ) : ConvexClosureVal topF x = ⊤ := by
  unfold ConvexClosureVal
  refine sInf_sub_top ?_
  rintro L ⟨S, hS, rfl⟩
  unfold ConvexClosureValOn
  refine sInf_sub_top ?_
  rintro L' ⟨lam, -, hsum, hdom, -, rfl⟩
  exfalso
  rcases S.eq_empty_or_nonempty with h | ⟨y, hy⟩
  · subst h; simp at hsum
  · exact hdom y hy rfl

end SharedCex

theorem solution : ¬ (∀ {V : Type} [Fintype V] [DecidableEq V]
    (f1 f2 : (V → ℤ) → WithTop ℝ) (_hf1 : MNaturalConvex f1)
    (_hf2 : MNaturalConvex f2) (x : V → ℝ),
    ∃ lam : (V → ℤ) → ℝ,
      (∀ y ∈ IntegralNeighborhoodFinset x, 0 ≤ lam y) ∧
      (∑ y ∈ IntegralNeighborhoodFinset x, lam y = 1) ∧
      (∀ v, ∑ y ∈ IntegralNeighborhoodFinset x, lam y * (y v : ℝ) = x v) ∧
      ConvexClosureVal f1 x =
        ((∑ y ∈ IntegralNeighborhoodFinset x, lam y * (f1 y).untopD 0 : ℝ) : WithTop ℝ) ∧
      ConvexClosureVal f2 x =
        ((∑ y ∈ IntegralNeighborhoodFinset x, lam y * (f2 y).untopD 0 : ℝ) : WithTop ℝ)) := by
  intro h
  obtain ⟨lam, -, -, -, h1, -⟩ := h SharedCex.topF SharedCex.topF SharedCex.topF_mnat
    SharedCex.topF_mnat (fun _ => 0)
  rw [SharedCex.topF_closure] at h1
  exact WithTop.top_ne_coe h1

#print axioms solution
