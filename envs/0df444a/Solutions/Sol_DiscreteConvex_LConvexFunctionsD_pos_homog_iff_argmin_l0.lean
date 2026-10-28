-- Prove2me | solution 1 for DiscreteConvex.LConvexFunctionsD.pos_homog_iff_argmin_l0
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-28T16:19:58.210978+00:00
-- url     : https://prove2.me/submissions/baa6798e-90db-441f-9d91-7c3414c6f772

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_PosHomogeneous
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_DomR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_ZeroLR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_LinearWeightR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_ArgMinR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_LConvexPolyhedron

open Classical
open scoped Pointwise

namespace DisPHA
open DiscreteConvex.LConvexFunctionsD

noncomputable def g0 : (Unit → ℝ) → WithTop ℝ := fun p => ((-|p ()| : ℝ) : WithTop ℝ)

lemma pos : PosHomogeneous g0 := by
  intro x t ht
  simp only [g0, PosScalarMul, abs_mul, abs_of_pos ht]
  congr 1; ring

lemma dom : (DomR g0).Nonempty := ⟨fun _ => 0, by simp [DomR, g0]⟩

lemma not_trf : ¬ TRFR g0 := by
  rintro ⟨r, hr⟩
  have h1 := hr (fun _ => 0) 1
  have h2 := hr (fun _ => 0) (-1)
  simp only [g0] at h1 h2
  rw [← WithTop.coe_mul, ← WithTop.coe_add, WithTop.coe_inj] at h1 h2
  norm_num at h1 h2
  linarith

lemma argmin_empty (x : Unit → ℝ) : ¬ (ArgMinR (LinearWeightR g0 (fun v => - x v))).Nonempty := by
  rintro ⟨p, hp⟩
  set N : ℝ := |p ()| + |x () * p ()| + 1
  have hN : 0 < N := by positivity
  obtain ⟨q, hq⟩ : ∃ q : ℝ, -|q| + x () * q ≤ -N := by
    rcases le_or_gt 0 (x ()) with h | h
    · refine ⟨-N, ?_⟩
      rw [abs_neg, abs_of_pos hN]; nlinarith
    · refine ⟨N, ?_⟩
      rw [abs_of_pos hN]; nlinarith
  have := hp (fun _ => q)
  simp only [LinearWeightR, g0, Fintype.sum_unique] at this
  rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe] at this
  have h1 := le_abs_self (x () * p ())
  have h2 := neg_abs_le (x () * p ())
  have h3 := abs_nonneg (p ())
  simp only [N] at hq
  nlinarith

end DisPHA

theorem solution : ¬ (∀ {V : Type} [Fintype V] [DecidableEq V] (g : (V → ℝ) → WithTop ℝ),
    DiscreteConvex.LConvexFunctionsD.PosHomogeneous g →
    (DiscreteConvex.LConvexFunctionsD.DomR g).Nonempty →
    (DiscreteConvex.LConvexFunctionsD.ZeroLR g ↔ ∀ x : V → ℝ,
      (DiscreteConvex.LConvexFunctionsD.ArgMinR
        (DiscreteConvex.LConvexFunctionsD.LinearWeightR g (fun v => - x v))).Nonempty →
      DiscreteConvex.LConvexFunctionsD.LConvexPolyhedron
        (DiscreteConvex.LConvexFunctionsD.ArgMinR
          (DiscreteConvex.LConvexFunctionsD.LinearWeightR g (fun v => - x v))))) := by
  intro h
  have := (h DisPHA.g0 DisPHA.pos DisPHA.dom).2 (fun x hx => absurd hx (DisPHA.argmin_empty x))
  exact DisPHA.not_trf this.2.1
