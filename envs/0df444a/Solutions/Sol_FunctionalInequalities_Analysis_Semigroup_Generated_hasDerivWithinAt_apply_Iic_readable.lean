-- Prove2me | solution 1 for FunctionalInequalities.Analysis.Semigroup.Generated.hasDerivWithinAt_apply_Iic_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:28:51.352748+00:00
-- url     : https://prove2.me/submissions/ab136d62-876b-4516-bc48-291a459da330

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Semigroup_Generated_Laws
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Semigroup_Generated_Domain
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Semigroup_Generated_TimeDerivative
import Theorems.Thm_FunctionalInequalities_Analysis_Semigroup_Generated_continuousOn_readable

section
noncomputable section
open InnerProductSpace
open scoped RealInnerProductSpace
section
variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
section
/-- **`P5`**: `P_0 = 1`.  `exp (-0 • L_s) = 1`, so the constant family `f` converges to `f`; `P1`
identifies the limit.  The route's `0 ≤ t` does not occur here. -/
theorem FunctionalInequalities.Analysis.Semigroup.Generated.zero_time (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set H₀)) (f : H₀) : Generated.apply T hT hd 0 f = f := by
  refine (Generated.eq_apply_of_tendsto T hT hd le_rfl f f ?_).symm
  intro ε hε
  refine ⟨1, one_pos, ?_⟩
  intro s hs _
  have hid : NormedSpace.exp (-(0 : ℝ) • yosida T hT hs) f = f := by
    rw [neg_zero, zero_smul, NormedSpace.exp_zero]
    rfl
  rw [hid, sub_self, norm_zero]
  exact hε
end
end
end
end

section
noncomputable section
open InnerProductSpace
open scoped RealInnerProductSpace LinearPMap
section
variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
  (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀))
/-- The right time derivative at `t ≥ 0` is `-A(P_t f)`. -/
theorem FunctionalInequalities.Analysis.Semigroup.Generated.right_derivative
    (f : (adjointComp T).domain) {t : ℝ} (ht : 0 ≤ t) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ‖h⁻¹ • (apply T hT hd (t + h) f - apply T hT hd t f) +
        adjointComp T ⟨apply T hT hd t f,
          preserves_domain T hT hd f ht⟩‖ < ε := by
  obtain ⟨δ, hδ, he⟩ := generator_limit_apply T hT hd f ht hε
  refine ⟨δ, hδ, fun h hh hhδ => ?_⟩
  rw [generator_comm T hT hd f ht, add_comm t h, add_time T hT hd hh.le ht]
  exact he h hh hhδ
end
end
end

noncomputable section
open Filter Topology Set
open scoped RealInnerProductSpace
variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
  (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀))
/-- The right derivative at time zero, in the normalized form
`‖h⁻¹ (P_h f - f) + A f‖ < ε` for small `h > 0`. -/
theorem FunctionalInequalities.Analysis.Semigroup.Generated.right_derivative_zero (f : (adjointComp T).domain) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ‖h⁻¹ • (apply T hT hd h f - f) + adjointComp T f‖ < ε := by
  obtain ⟨δ, hδ, hr⟩ := right_derivative T hT hd f le_rfl hε
  refine ⟨δ, hδ, fun h hh hhδ => ?_⟩
  have h0 : (⟨apply T hT hd 0 f, preserves_domain T hT hd f le_rfl⟩ :
      (adjointComp T).domain) = f := Subtype.ext (zero_time T hT hd f)
  have := hr h hh hhδ
  rwa [zero_add, h0, zero_time] at this
/-- **Left derivative of the orbit**: for `f ∈ D(A)` and `t > 0`,
`d/ds P_s f = -A (P_t f)` from the left at `s = t`. -/
theorem solution (f : (FunctionalInequalities.Analysis.Semigroup.adjointComp T).domain) {t : ℝ} (ht : 0 < t) :
    HasDerivWithinAt (fun s => FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd s f)
      (-FunctionalInequalities.Analysis.Semigroup.adjointComp T ⟨FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t f, FunctionalInequalities.Analysis.Semigroup.Generated.preserves_domain T hT hd f ht.le⟩) (Iic t) t := by
  rw [hasDerivWithinAt_iff_tendsto_slope, Iic_sdiff_right, Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ₁, hδ₁, h₁⟩ := FunctionalInequalities.Analysis.Semigroup.Generated.right_derivative_zero T hT hd f (half_pos hε)
  obtain ⟨δ₂, hδ₂, h₂⟩ := Metric.continuousWithinAt_iff.mp
    ((FunctionalInequalities.Analysis.Semigroup.Generated.continuousOn_readable T hT hd (FunctionalInequalities.Analysis.Semigroup.adjointComp T f)) t ht.le) (ε / 2) (half_pos hε)
  refine ⟨min (min δ₁ δ₂) t, lt_min (lt_min hδ₁ hδ₂) ht, fun s hs hsd => ?_⟩
  have hh : 0 < t - s := sub_pos.mpr hs
  have hlt : t - s < min (min δ₁ δ₂) t := by
    rw [Real.dist_eq, abs_of_neg (by linarith)] at hsd; linarith
  have hs0 : 0 ≤ s := by linarith [min_le_right (min δ₁ δ₂) t]
  set h := t - s with hhdef
  have hPt : FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t f = FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd s (FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd h f) := by
    rw [← FunctionalInequalities.Analysis.Semigroup.Generated.add_time T hT hd hs0 hh.le]; congr 1; ring
  have key : slope (fun s => FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd s f) t s =
      FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd s (h⁻¹ • (FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd h (f : H₀) - f)) := by
    rw [slope_def_module, hPt, FunctionalInequalities.Analysis.Semigroup.Generated.map_smul T hT hd hs0, FunctionalInequalities.Analysis.Semigroup.Generated.map_sub T hT hd hs0,
      show s - t = -h by rw [hhdef]; ring, inv_neg, neg_smul, ← smul_neg, neg_sub]
  rw [dist_eq_norm, key, FunctionalInequalities.Analysis.Semigroup.Generated.generator_comm T hT hd f ht.le, sub_neg_eq_add]
  have hsplit : FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd s (h⁻¹ • (FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd h (f : H₀) - f)) +
      FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t (FunctionalInequalities.Analysis.Semigroup.adjointComp T f) =
      FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd s (h⁻¹ • (FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd h (f : H₀) - f) + FunctionalInequalities.Analysis.Semigroup.adjointComp T f) +
        (FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t (FunctionalInequalities.Analysis.Semigroup.adjointComp T f) - FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd s (FunctionalInequalities.Analysis.Semigroup.adjointComp T f)) := by
    rw [FunctionalInequalities.Analysis.Semigroup.Generated.map_add T hT hd hs0]; abel
  have hA : ‖FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd s (h⁻¹ • (FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd h (f : H₀) - f) + FunctionalInequalities.Analysis.Semigroup.adjointComp T f)‖ <
      ε / 2 :=
    (FunctionalInequalities.Analysis.Semigroup.Generated.norm_apply_le T hT hd hs0 _).trans_lt (h₁ h hh (hlt.trans_le
      ((min_le_left _ _).trans (min_le_left _ _))))
  have hB : ‖FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t (FunctionalInequalities.Analysis.Semigroup.adjointComp T f) - FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd s (FunctionalInequalities.Analysis.Semigroup.adjointComp T f)‖ < ε / 2 := by
    rw [← dist_eq_norm, dist_comm]
    refine h₂ (mem_Ici.mpr hs0) ?_
    rw [Real.dist_eq, abs_of_neg (by linarith)]
    linarith [(min_le_left (min δ₁ δ₂) t).trans (min_le_right δ₁ δ₂)]
  rw [hsplit]
  exact (norm_add_le _ _).trans_lt (by linarith)
