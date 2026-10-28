-- Prove2me | solution 1 for FunctionalInequalities.Analysis.subgradient_mem_interior_of_strictConvexOn_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:31:47.730457+00:00
-- url     : https://prove2.me/submissions/3cac42d3-9c75-4281-9950-cb6c165cf0c4

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Caffarelli
import Theorems.Thm_FunctionalInequalities_Analysis_exists_subgradient_slope_le_inner_add_readable

noncomputable section
open Set Metric
open scoped RealInnerProductSpace
section LT11F1StrictConvexityElementary
open Set
section InnerProduct
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
private theorem FunctionalInequalities.Analysis.strict_supporting_inequality {u : E → ℝ} (hstrict : StrictConvexOn ℝ univ u)
    {x p y : E} (hp : ∀ t, u x + ⟪p, t - x⟫ ≤ u t) (hy : y ≠ x) :
    u x + ⟪p, y - x⟫ < u y := by
  by_contra hn
  have heq : u y = u x + ⟪p, y - x⟫ :=
    le_antisymm (le_of_not_gt hn) (hp y)
  have hm :
      u ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) <
        (1 / 2 : ℝ) • u x + (1 / 2 : ℝ) • u y :=
    hstrict.2 (mem_univ x) (mem_univ y) hy.symm
      (by norm_num) (by norm_num) (by norm_num)
  have hs := hp ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y)
  simp only [smul_eq_mul] at hm
  simp only [inner_sub_right, inner_add_right, real_inner_smul_right] at hs heq
  linarith
section FiniteDimensional
variable [FiniteDimensional ℝ E]
/-- **Slopes of a strictly convex function lie in the interior of a convex slope range** (weak Letwin
route): if all subgradients of the strictly convex `u` lie in a convex `K` with nonempty
interior, they lie in `interior K`. -/
theorem solution {u : E → ℝ}
    (hstrict : StrictConvexOn ℝ univ u) {K : Set E} (hKc : Convex ℝ K)
    (hKint : (interior K).Nonempty)
    (hK : ∀ x p : E, (∀ y, u x + ⟪p, y - x⟫ ≤ u y) → p ∈ K)
    {x p : E} (hp : ∀ y, u x + ⟪p, y - x⟫ ≤ u y) : p ∈ interior K := by
  by_contra hn
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hKc.interior isOpen_interior hn
  have hbound : ∀ q ∈ K, f q ≤ f p := by
    have hcl : closure (interior K) ⊆ {q | f q ≤ f p} :=
      closure_minimal (fun q hq => (hf q hq).le)
        (isClosed_le f.continuous continuous_const)
    intro q hq
    apply hcl
    rw [hKc.closure_interior_eq_closure_of_nonempty_interior hKint]
    exact subset_closure hq
  let v : E := (InnerProductSpace.toDual ℝ E).symm f
  have hvf : ∀ q : E, ⟪v, q⟫ = f q := by
    intro q
    exact InnerProductSpace.toDual_symm_apply
  have hv : v ≠ 0 := by
    intro hvzero
    obtain ⟨q, hq⟩ := hKint
    have hqp := hf q hq
    rw [← hvf q, ← hvf p, hvzero, inner_zero_left, inner_zero_left] at hqp
    exact (lt_irrefl (0 : ℝ)) hqp
  have hxv : x + v ≠ x := add_ne_left.mpr hv
  have hlt := FunctionalInequalities.Analysis.strict_supporting_inequality hstrict hp hxv
  rw [add_sub_cancel_left] at hlt
  obtain ⟨q, hq, _⟩ :=
    FunctionalInequalities.Analysis.exists_subgradient_slope_le_inner_add_readable hstrict.convexOn (x + v) (0 : E)
  have hback := hq x
  have hsub : x - (x + v) = -v := by abel
  rw [hsub, inner_neg_right] at hback
  have hqp := hbound q (hK (x + v) q hq)
  have hpv : ⟪p, v⟫ = f p := (real_inner_comm v p).trans (hvf p)
  have hqv : ⟪q, v⟫ = f q := (real_inner_comm v q).trans (hvf q)
  rw [hpv] at hlt
  rw [hqv] at hback
  linarith
