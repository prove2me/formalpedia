-- Prove2me | solution 1 for FunctionalInequalities.Analysis.Semigroup.Generated.hasDerivAt_inner_apply_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:31:11.82792+00:00
-- url     : https://prove2.me/submissions/335570f6-e42f-4c51-a870-7705a5721a60

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Semigroup_Generated_Curvature
import Theorems.Thm_FunctionalInequalities_Analysis_Semigroup_Generated_hasDerivAt_apply_of_pos_readable

noncomputable section
open Filter Topology Set
open scoped RealInnerProductSpace
variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
  (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀))
/-- The energy derivative: for `f ∈ D(A)` and `s > 0`,
`d/ds ⟪P_s (A f), P_s f⟫ = -2 ‖A (P_s f)‖²`. -/
theorem solution (f : (FunctionalInequalities.Analysis.Semigroup.adjointComp T).domain) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun r => ⟪FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd r (FunctionalInequalities.Analysis.Semigroup.adjointComp T f), FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd r f⟫)
      (-2 * ‖FunctionalInequalities.Analysis.Semigroup.adjointComp T ⟨FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd s f, FunctionalInequalities.Analysis.Semigroup.Generated.preserves_domain T hT hd f hs.le⟩‖ ^ 2) s := by
  let y : (FunctionalInequalities.Analysis.Semigroup.adjointComp T).domain :=
    ⟨FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd s f, FunctionalInequalities.Analysis.Semigroup.Generated.preserves_domain T hT hd f hs.le⟩

  let z : (FunctionalInequalities.Analysis.Semigroup.adjointComp T).domain :=
    ⟨FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd s (FunctionalInequalities.Analysis.Semigroup.adjointComp T f),
      FunctionalInequalities.Analysis.Semigroup.Generated.mem_adjointComp_domain_apply_of_pos T hT hd (FunctionalInequalities.Analysis.Semigroup.adjointComp T f) hs⟩

  have hgen : FunctionalInequalities.Analysis.Semigroup.adjointComp T y = FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd s (FunctionalInequalities.Analysis.Semigroup.adjointComp T f) := by
    dsimp [y]
    exact FunctionalInequalities.Analysis.Semigroup.Generated.generator_comm T hT hd f hs.le

  have hz : (z : H₀) = FunctionalInequalities.Analysis.Semigroup.adjointComp T y := by
    dsimp [z]
    exact hgen.symm

  have h1 :
      HasDerivAt (fun r => FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd r (FunctionalInequalities.Analysis.Semigroup.adjointComp T f))
        (-FunctionalInequalities.Analysis.Semigroup.adjointComp T z) s := by
    dsimp [z]
    exact FunctionalInequalities.Analysis.Semigroup.Generated.hasDerivAt_apply_of_pos_readable T hT hd (FunctionalInequalities.Analysis.Semigroup.adjointComp T f) hs

  have h2 :
      HasDerivAt (fun r => FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd r (f : H₀))
        (-FunctionalInequalities.Analysis.Semigroup.adjointComp T y) s := by
    dsimp [y]
    exact FunctionalInequalities.Analysis.Semigroup.Generated.hasDerivAt_apply_of_pos_readable T hT hd (f : H₀) hs

  have hsymm :
      ⟪FunctionalInequalities.Analysis.Semigroup.adjointComp T z, (y : H₀)⟫ =
        ⟪(z : H₀), FunctionalInequalities.Analysis.Semigroup.adjointComp T y⟫ := by
    calc
      ⟪FunctionalInequalities.Analysis.Semigroup.adjointComp T z, (y : H₀)⟫ =
          ⟪T ⟨(z : H₀), z.2.2⟩, T ⟨(y : H₀), y.2.2⟩⟫ :=
        FunctionalInequalities.Analysis.Semigroup.inner_adjointComp (T := T) hd z y.2.2
      _ = ⟪T ⟨(y : H₀), y.2.2⟩, T ⟨(z : H₀), z.2.2⟩⟫ := by
        rw [real_inner_comm]
      _ = ⟪FunctionalInequalities.Analysis.Semigroup.adjointComp T y, (z : H₀)⟫ :=
        (FunctionalInequalities.Analysis.Semigroup.inner_adjointComp (T := T) hd y z.2.2).symm
      _ = ⟪(z : H₀), FunctionalInequalities.Analysis.Semigroup.adjointComp T y⟫ := by
        rw [real_inner_comm]

  have hfirst :
      ⟪FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd s (FunctionalInequalities.Analysis.Semigroup.adjointComp T f), -FunctionalInequalities.Analysis.Semigroup.adjointComp T y⟫ =
        -‖FunctionalInequalities.Analysis.Semigroup.adjointComp T y‖ ^ 2 := by
    calc
      ⟪FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd s (FunctionalInequalities.Analysis.Semigroup.adjointComp T f), -FunctionalInequalities.Analysis.Semigroup.adjointComp T y⟫ =
          ⟪FunctionalInequalities.Analysis.Semigroup.adjointComp T y, -FunctionalInequalities.Analysis.Semigroup.adjointComp T y⟫ := by
        rw [hgen]
      _ = -⟪FunctionalInequalities.Analysis.Semigroup.adjointComp T y, FunctionalInequalities.Analysis.Semigroup.adjointComp T y⟫ := by
        rw [inner_neg_right]
      _ = -‖FunctionalInequalities.Analysis.Semigroup.adjointComp T y‖ ^ 2 := by
        rw [real_inner_self_eq_norm_sq]

  have hsecond :
      ⟪-FunctionalInequalities.Analysis.Semigroup.adjointComp T z, FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd s f⟫ =
        -‖FunctionalInequalities.Analysis.Semigroup.adjointComp T y‖ ^ 2 := by
    calc
      ⟪-FunctionalInequalities.Analysis.Semigroup.adjointComp T z, FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd s f⟫ =
          -⟪FunctionalInequalities.Analysis.Semigroup.adjointComp T z, (y : H₀)⟫ := by
        dsimp [y]
        rw [inner_neg_left]
      _ = -⟪(z : H₀), FunctionalInequalities.Analysis.Semigroup.adjointComp T y⟫ := by
        rw [hsymm]
      _ = -⟪FunctionalInequalities.Analysis.Semigroup.adjointComp T y, FunctionalInequalities.Analysis.Semigroup.adjointComp T y⟫ := by
        rw [hz]
      _ = -‖FunctionalInequalities.Analysis.Semigroup.adjointComp T y‖ ^ 2 := by
        rw [real_inner_self_eq_norm_sq]

  have hder :=
    h1.inner ℝ h2

  have heq :
      ⟪FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd s (FunctionalInequalities.Analysis.Semigroup.adjointComp T f), -FunctionalInequalities.Analysis.Semigroup.adjointComp T y⟫ +
          ⟪-FunctionalInequalities.Analysis.Semigroup.adjointComp T z, FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd s f⟫ =
        -2 * ‖FunctionalInequalities.Analysis.Semigroup.adjointComp T y‖ ^ 2 := by
    rw [hfirst, hsecond]
    ring

  have hresult :
      HasDerivAt
        (fun r => ⟪FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd r (FunctionalInequalities.Analysis.Semigroup.adjointComp T f), FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd r f⟫)
        (-2 * ‖FunctionalInequalities.Analysis.Semigroup.adjointComp T y‖ ^ 2) s :=
    hder.congr_deriv heq

  simpa [y] using hresult
