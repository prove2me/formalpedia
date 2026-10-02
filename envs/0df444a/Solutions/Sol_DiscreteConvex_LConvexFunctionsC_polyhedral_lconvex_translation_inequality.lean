-- Prove2me | solution 1 for DiscreteConvex.LConvexFunctionsC.polyhedral_lconvex_translation_inequality
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T03:34:18.655898+00:00
-- url     : https://prove2.me/submissions/1fdbc57c-9f65-4276-9408-b5148debc80f

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_SBFR
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_TRFR

set_option autoImplicit false

universe u

open Classical DiscreteConvex.LConvexFunctionsC in
theorem solution {V : Type u} [Fintype V] [DecidableEq V] (g : (V → ℝ) → WithTop ℝ) (hg : SBFR g ∧ TRFR g) :
    ∀ p q : V → ℝ, ∀ alpha : ℝ,
      g p + g q ≥ g (fun v => max (p v - alpha) (q v)) + g (fun v => min (p v) (q v + alpha)) := by
  intro p q alpha
  obtain ⟨hs, r, hr⟩ := hg
  set p' : V → ℝ := fun v => p v + (-alpha) with hp'
  have h1 := hs p' q
  have hsup : p' ⊔ q = fun v => max (p v - alpha) (q v) := by
    funext v; simp [hp', sub_eq_add_neg]
  set m : V → ℝ := fun v => min (p v) (q v + alpha) with hm
  have hinf : p' ⊓ q = fun v => m v + (-alpha) := by
    funext v
    simp only [hp', hm, Pi.inf_apply]
    rw [← min_add_add_right]
    simp
  rw [hsup, hinf, hr m (-alpha), hr p (-alpha)] at h1
  have hne : (((-alpha : ℝ) : WithTop ℝ) * (r : WithTop ℝ)) ≠ ⊤ := by
    rw [← WithTop.coe_mul]; exact WithTop.coe_ne_top
  have h2 : g p + g q + (((-alpha : ℝ) : WithTop ℝ) * (r : WithTop ℝ)) ≥
      g (fun v => max (p v - alpha) (q v)) + g m + (((-alpha : ℝ) : WithTop ℝ) * (r : WithTop ℝ)) := by
    calc g (fun v => max (p v - alpha) (q v)) + g m + (((-alpha : ℝ) : WithTop ℝ) * (r : WithTop ℝ))
        = g (fun v => max (p v - alpha) (q v)) + (g m + (((-alpha : ℝ) : WithTop ℝ) * (r : WithTop ℝ))) := by
          rw [add_assoc]
      _ ≤ g p + (((-alpha : ℝ) : WithTop ℝ) * (r : WithTop ℝ)) + g q := h1
      _ = g p + g q + (((-alpha : ℝ) : WithTop ℝ) * (r : WithTop ℝ)) := by
          rw [add_assoc, add_comm (((-alpha : ℝ) : WithTop ℝ) * (r : WithTop ℝ)), ← add_assoc]
  exact (WithTop.add_le_add_iff_right hne).1 h2
