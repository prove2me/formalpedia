-- Prove2me | solution 1 for DiscreteConvex.LConvexFunctionsD.integral_lconvex_iff_integral_argmin
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-28T16:20:19.235934+00:00
-- url     : https://prove2.me/submissions/4edade24-c7f4-447a-9834-82765ecbf925

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_DomR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_IsIntegralPolyhedron
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_LinearWeightR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_ArgMinR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_LConvexIntegralR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_LConvexPolyhedron

open Classical
open scoped Pointwise

namespace DisILA
open DiscreteConvex.LConvexFunctionsD

noncomputable def g0 : (Unit → ℝ) → WithTop ℝ := fun p => ((-(p ()) ^ 2 : ℝ) : WithTop ℝ)

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
  have := hp (fun _ => |p ()| + |x ()| + 1)
  simp only [LinearWeightR, g0, Fintype.sum_unique] at this
  rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe] at this
  have h1 := le_abs_self (x ())
  have h2 := neg_abs_le (x ())
  have h3 := le_abs_self (p ())
  have h4 := neg_abs_le (p ())
  have h5 := abs_nonneg (p ())
  have h6 := abs_nonneg (x ())
  have h7 := neg_abs_le (x () * p ())
  rw [abs_mul] at h7
  have h8 := sq_abs (p ())
  set q := |p ()| + |x ()| + 1 with hq
  have hq1 : 1 ≤ q := by linarith
  have h9 : x () * q ≤ |x ()| * q := mul_le_mul_of_nonneg_right h1 (by linarith)
  nlinarith [mul_nonneg h5 h6]

end DisILA

theorem solution : ¬ (∀ {V : Type} [Fintype V] [DecidableEq V] (g : (V → ℝ) → WithTop ℝ),
    (DiscreteConvex.LConvexFunctionsD.DomR g).Nonempty →
    (DiscreteConvex.LConvexFunctionsD.LConvexIntegralR g ↔
      ∀ x : V → ℝ, (DiscreteConvex.LConvexFunctionsD.ArgMinR
          (DiscreteConvex.LConvexFunctionsD.LinearWeightR g (fun v => - x v))).Nonempty →
        (DiscreteConvex.LConvexFunctionsD.LConvexPolyhedron (DiscreteConvex.LConvexFunctionsD.ArgMinR
            (DiscreteConvex.LConvexFunctionsD.LinearWeightR g (fun v => - x v))) ∧
          DiscreteConvex.LConvexFunctionsD.IsIntegralPolyhedron (DiscreteConvex.LConvexFunctionsD.ArgMinR
            (DiscreteConvex.LConvexFunctionsD.LinearWeightR g (fun v => - x v)))))) := by
  intro h
  have := (h DisILA.g0 DisILA.dom).2 (fun x hx => absurd hx (DisILA.argmin_empty x))
  exact DisILA.not_trf this.2.1
