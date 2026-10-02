-- Prove2me | solution 1 for DiscreteConvex.MConvexFunctionsC.mconvex_argmin_is_mconvex_set
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T05:00:43.718971+00:00
-- url     : https://prove2.me/submissions/575db507-6960-4a1a-9d03-f06469834a08

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_ExchangeAxiomB
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_ArgMinOn

set_option autoImplicit false

open scoped Pointwise
open Classical in
open DiscreteConvex.MConvexFunctionsC in
theorem solution : ¬ (∀ {V : Type} [Fintype V] [DecidableEq V]
    (f : (V → ℤ) → WithTop ℝ) (hf : MExchangeAxiom f)
    (hne : (ArgMinOn f).Nonempty), ExchangeAxiomB (ArgMinOn f)) := by
  intro h
  have hB := h (V := Unit) (fun _ => ⊤)
    (fun x hx _ _ _ _ => absurd rfl hx)
    ⟨fun _ => 0, fun _ => le_rfl⟩
  obtain ⟨v, hv, -⟩ := hB (fun _ => 1) (fun _ => le_rfl) (fun _ => 0) (fun _ => le_rfl) ()
    (by simp [DiscreteConvex.MConvexFunctionsC.SuppPos])
  simp [DiscreteConvex.MConvexFunctionsC.SuppNeg] at hv
