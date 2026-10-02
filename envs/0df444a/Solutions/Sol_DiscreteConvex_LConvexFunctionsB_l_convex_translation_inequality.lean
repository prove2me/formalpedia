-- Prove2me | solution 1 for DiscreteConvex.LConvexFunctionsB.l_convex_translation_inequality
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T04:33:06.697352+00:00
-- url     : https://prove2.me/submissions/fd2f05f2-2595-4134-ba68-64b6af2256a7

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_SBF
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_TRF

set_option autoImplicit false

namespace DiscreteConvex.LConvexFunctionsB

open Classical
open scoped Pointwise

theorem trf_shift_aux {V : Type*} (g : (V → ℤ) → WithTop ℝ) (r : ℝ)
    (hr : ∀ p : V → ℤ, g (p + 1) = g p + (r : WithTop ℝ)) :
    ∀ n : ℤ, ∀ p : V → ℤ, g (p + fun _ => n) = g p + (((n : ℝ) * r : ℝ) : WithTop ℝ) := by
  intro n
  induction n using Int.induction_on with
  | zero =>
    intro p
    have : (p + fun _ => (0:ℤ)) = p := by funext v; simp
    rw [this]; simp
  | succ k ih =>
    intro p
    have h1 : (p + fun _ => ((k:ℤ) + 1)) = (p + fun _ => (k:ℤ)) + 1 := by
      funext v; simp; ring
    rw [h1, hr, ih, add_assoc, ← WithTop.coe_add]
    congr 2
    push_cast; ring
  | pred k ih =>
    intro p
    have h1 : (p + fun _ => (-(k:ℤ))) = (p + fun _ => (-(k:ℤ) - 1)) + 1 := by
      funext v; simp only [Pi.add_apply, Pi.one_apply]; ring
    have h2 := ih p
    rw [h1, hr] at h2
    have h3 : g (p + fun _ => (-(k:ℤ) - 1))
        = g (p + fun _ => (-(k:ℤ) - 1)) + (r : WithTop ℝ) + ((-r : ℝ) : WithTop ℝ) := by
      rw [add_assoc, ← WithTop.coe_add]; simp
    rw [h3, h2, add_assoc, ← WithTop.coe_add]
    congr 2
    push_cast; ring

theorem lconv_trans_ineq_aux {V : Type*} [Fintype V] [DecidableEq V]
    (g : (V → ℤ) → WithTop ℝ) (hg : SBF g ∧ TRF g) :
    ∀ p q : V → ℤ, ∀ alpha : ℤ,
      g p + g q ≥ g (fun v => max (p v - alpha) (q v)) + g (fun v => min (p v) (q v + alpha)) := by
  obtain ⟨hS, r, hr⟩ := hg
  intro p q alpha
  have hsh := trf_shift_aux g r hr
  set p' : V → ℤ := p + fun _ => -alpha with hp'
  have e1 : (fun v => max (p v - alpha) (q v)) = p' ⊔ q := by
    funext v; simp [hp', sub_eq_add_neg]
  have e2 : (fun v => min (p v) (q v + alpha)) = (p' ⊓ q) + fun _ => alpha := by
    funext v; simp only [hp', Pi.add_apply, Pi.inf_apply]; omega
  have e3 : p = p' + fun _ => alpha := by funext v; simp [hp']
  have key := hS p' q
  rw [e1, e2, hsh]
  have hp : g p = g p' + (((alpha : ℝ) * r : ℝ) : WithTop ℝ) := by
    conv_lhs => rw [e3]
    exact hsh alpha p'
  rw [hp]
  have : g p' + (((alpha : ℝ) * r : ℝ) : WithTop ℝ) + g q
      = (g p' + g q) + (((alpha : ℝ) * r : ℝ) : WithTop ℝ) := by
    rw [add_assoc, add_comm (((alpha : ℝ) * r : ℝ) : WithTop ℝ), ← add_assoc]
  rw [this, ← add_assoc]
  exact add_le_add key le_rfl

end DiscreteConvex.LConvexFunctionsB

open Classical in
open scoped Pointwise in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (g : (V → ℤ) → WithTop ℝ) (hg : DiscreteConvex.LConvexFunctionsB.SBF g ∧ DiscreteConvex.LConvexFunctionsB.TRF g) :
    ∀ p q : V → ℤ, ∀ alpha : ℤ,
      g p + g q ≥ g (fun v => max (p v - alpha) (q v)) + g (fun v => min (p v) (q v + alpha)) := by
  exact DiscreteConvex.LConvexFunctionsB.lconv_trans_ineq_aux g hg
