-- Prove2me | solution 1 for FunctionalInequalities.Analysis.Semigroup.Generated.norm_map_apply_sq_eq_inner_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:28:28.40298+00:00
-- url     : https://prove2.me/submissions/325b5c47-73a6-48f9-a750-14aece246cb2

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Semigroup_Generated_Curvature

noncomputable section
open Filter Topology Set
open scoped RealInnerProductSpace
variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
  (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀))
/-- The energy along the flow from `f ∈ D(A)` is `‖T (P_r f)‖² = ⟪P_r (A f), P_r f⟫`. -/
theorem solution (f : (FunctionalInequalities.Analysis.Semigroup.adjointComp T).domain) {r : ℝ} (hr : 0 ≤ r) :
    ‖T ⟨FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd r f, (FunctionalInequalities.Analysis.Semigroup.Generated.preserves_domain T hT hd f hr).2⟩‖ ^ 2 =
      ⟪FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd r (FunctionalInequalities.Analysis.Semigroup.adjointComp T f), FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd r f⟫ := by
  let x : (FunctionalInequalities.Analysis.Semigroup.adjointComp T).domain :=
    ⟨FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd r f, FunctionalInequalities.Analysis.Semigroup.Generated.preserves_domain T hT hd f hr⟩

  have hinner :
      ⟪FunctionalInequalities.Analysis.Semigroup.adjointComp T x, (x : H₀)⟫ =
        ‖T ⟨(x : H₀), x.2.2⟩‖ ^ 2 := by
    simpa only [real_inner_self_eq_norm_sq] using
      (FunctionalInequalities.Analysis.Semigroup.inner_adjointComp (T := T) hd x x.2.2)

  have hgen :
      FunctionalInequalities.Analysis.Semigroup.adjointComp T x = FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd r (FunctionalInequalities.Analysis.Semigroup.adjointComp T f) := by
    dsimp [x]
    exact FunctionalInequalities.Analysis.Semigroup.Generated.generator_comm T hT hd f hr

  have hsub :
      (⟨FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd r f, (FunctionalInequalities.Analysis.Semigroup.Generated.preserves_domain T hT hd f hr).2⟩ : T.domain) =
        ⟨(x : H₀), x.2.2⟩ := by
    apply Subtype.ext
    rfl

  calc
    ‖T ⟨FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd r f, (FunctionalInequalities.Analysis.Semigroup.Generated.preserves_domain T hT hd f hr).2⟩‖ ^ 2 =
        ‖T ⟨(x : H₀), x.2.2⟩‖ ^ 2 := by rw [hsub]
    _ = ⟪FunctionalInequalities.Analysis.Semigroup.adjointComp T x, (x : H₀)⟫ := hinner.symm
    _ = ⟪FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd r (FunctionalInequalities.Analysis.Semigroup.adjointComp T f), FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd r f⟫ := by
      rw [hgen]
