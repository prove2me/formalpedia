-- Prove2me | solution 1 for BitcoinOligopoly.EoS.f_decreasing
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T15:18:20.260826+00:00
-- url     : https://prove2.me/submissions/2d549e4d-e0ae-43ae-87d4-cfb601c2bb3b

import Mathlib
import Definitions.Def_BitcoinOligopoly_EoS_Model

set_option autoImplicit false
open BitcoinOligopoly.EoS

namespace EoSAux

lemma f_anti (β : ℝ) (hβ0 : 0 ≤ β) :
    StrictAntiOn (fun x : ℝ => x ^ β * (1 - x)) (Set.Ioo (β / (1 + β)) 1) := by
  have hD : Convex ℝ (Set.Ioo (β / (1 + β)) 1) := convex_Ioo _ _
  have hpos : ∀ x ∈ Set.Ioo (β / (1 + β)) 1, 0 < x := by
    intro x hx
    exact lt_of_le_of_lt (div_nonneg hβ0 (by linarith)) hx.1
  refine strictAntiOn_of_deriv_neg hD ?_ ?_
  · intro x hx
    have := hpos x hx
    exact ((Real.continuousAt_rpow_const x β (Or.inl this.ne')).mul
      (continuousAt_const.sub continuousAt_id)).continuousWithinAt
  · intro x hx
    rw [interior_Ioo] at hx
    have hx0 := hpos x hx
    have hd : HasDerivAt (fun x : ℝ => x ^ β * (1 - x))
        (β * x ^ (β - 1) * (1 - x) + x ^ β * (-1)) x := by
      have h1 := Real.hasDerivAt_rpow_const (x := x) (p := β) (Or.inl hx0.ne')
      have h2 : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by
        simpa using (hasDerivAt_id x).const_sub 1
      exact h1.mul h2
    rw [hd.deriv]
    have hxb : x ^ β = x ^ (β - 1) * x := by
      rw [Real.rpow_sub_one hx0.ne']; field_simp
    have hlt : β * (1 - x) - x < 0 := by
      have := hx.1
      rw [div_lt_iff₀ (by linarith)] at this
      nlinarith
    have hp : 0 < x ^ (β - 1) := Real.rpow_pos_of_pos hx0 _
    rw [hxb]
    nlinarith [mul_neg_of_pos_of_neg hp hlt]

lemma f_anti' (α : ℝ) (hα : 1 ≤ α) :
    StrictAntiOn (fShape α) (Set.Ioo ((1 - 1 / α) / (1 + (1 - 1 / α))) 1) := by
  have hα0 : 0 < α := by linarith
  have hβ0 : 0 ≤ 1 - 1 / α := by
    have : 1 / α ≤ 1 := by rw [div_le_one hα0]; exact hα
    linarith
  exact f_anti _ hβ0

end EoSAux

theorem solution (α : ℝ) (hα : 1 ≤ α) :
    StrictAntiOn (fShape α) (Set.Ioo (1 - 1 / α) 1) := by
  have hα0 : 0 < α := by linarith
  have hβ0 : 0 ≤ 1 - 1 / α := by
    have : 1 / α ≤ 1 := by rw [div_le_one hα0]; exact hα
    linarith
  refine (EoSAux.f_anti' α hα).mono ?_
  intro x hx
  refine ⟨lt_of_le_of_lt ?_ hx.1, hx.2⟩
  rw [div_le_iff₀ (by linarith)]; nlinarith
