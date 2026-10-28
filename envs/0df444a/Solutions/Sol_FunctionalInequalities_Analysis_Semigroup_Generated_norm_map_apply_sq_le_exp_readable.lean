-- Prove2me | solution 1 for FunctionalInequalities.Analysis.Semigroup.Generated.norm_map_apply_sq_le_exp_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:33:29.388758+00:00
-- url     : https://prove2.me/submissions/766b518d-1bc6-443d-9619-543f59d3e54c

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Semigroup_Generated_FormDomain
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Semigroup_Generated_Curvature
import Theorems.Thm_FunctionalInequalities_Analysis_Semigroup_Generated_norm_map_apply_sq_le_exp_of_mem_adjointComp_readable

section
noncomputable section
open InnerProductSpace
open scoped RealInnerProductSpace LinearPMap
section
variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
  (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀))
/-- **form-energy contraction: the semigroup contracts the energy on the whole form domain.**  For `f ∈ D(T)`,
`t ≥ 0` and any witness of `P_t f ∈ D(T)`, `‖T (P_t f)‖ ≤ ‖T f‖`.  The gradient is `T` in the
closed-operator sense; no classical representative is claimed. -/
theorem FunctionalInequalities.Analysis.Semigroup.Generated.norm_map_apply_le (f : T.domain) {t : ℝ} (ht : 0 ≤ t)
    (hft : apply T hT hd t (f : H₀) ∈ T.domain) :
    ‖T ⟨apply T hT hd t (f : H₀), hft⟩‖ ≤ ‖T f‖ := by
  obtain ⟨_, hle⟩ := exists_mem_domain_norm_map_apply_le T hT hd f ht
  exact hle
end
end
end

noncomputable section
open Filter Topology Set
open scoped RealInnerProductSpace
variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
  (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀))
/-- Exponential energy decay on the whole form domain `D(T)` under the curvature bound. -/
theorem solution {ρ : ℝ}
    (hcurv : ∀ y : (FunctionalInequalities.Analysis.Semigroup.adjointComp T).domain, ρ * ‖T ⟨y, y.2.2⟩‖ ^ 2 ≤ ‖FunctionalInequalities.Analysis.Semigroup.adjointComp T y‖ ^ 2)
    (f : T.domain) {t : ℝ} (ht : 0 ≤ t) :
    ‖T ⟨FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t f, FunctionalInequalities.Analysis.Semigroup.Generated.preserves_form_domain T hT hd f ht⟩‖ ^ 2 ≤
      Real.exp (-2 * ρ * t) * ‖T f‖ ^ 2 := by
  obtain ⟨u, hu, hu₁, hu₂⟩ :=
    FunctionalInequalities.Analysis.Semigroup.Generated.exists_seq_mem_adjointComp_domain_tendsto_graph T hT hd f

  let v : ℕ → T.domain := fun n =>
    ⟨u n - (f : H₀), T.domain.sub_mem (hu n).2 f.2⟩

  let q : ℕ → T.domain := fun n =>
    ⟨FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t (u n),
      FunctionalInequalities.Analysis.Semigroup.Generated.preserves_form_domain T hT hd ⟨u n, (hu n).2⟩ ht⟩

  let q₀ : T.domain :=
    ⟨FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t (f : H₀), FunctionalInequalities.Analysis.Semigroup.Generated.preserves_form_domain T hT hd f ht⟩

  have hmap_sub : ∀ n, T (v n) =
      T ⟨u n, (hu n).2⟩ - T f := by
    intro n
    dsimp [v]
    exact T.map_sub ⟨u n, (hu n).2⟩ f

  have happly_sub : ∀ n,
      FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t (u n - (f : H₀)) =
        FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t (u n) - FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t (f : H₀) := by
    intro n
    exact FunctionalInequalities.Analysis.Semigroup.Generated.map_sub T hT hd ht (u n) (f : H₀)

  have hq_sub : ∀ n, q n - q₀ =
      ⟨FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t (u n - (f : H₀)),
        FunctionalInequalities.Analysis.Semigroup.Generated.preserves_form_domain T hT hd (v n) ht⟩ := by
    intro n
    apply Subtype.ext
    dsimp [q, q₀, v]
    exact (happly_sub n).symm

  have hbound : ∀ n,
      ‖T (q n) - T q₀‖ ≤ ‖T (v n)‖ := by
    intro n
    calc
      ‖T (q n) - T q₀‖ = ‖T (q n - q₀)‖ := by
        rw [T.map_sub]
      _ = ‖T ⟨FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t (u n - (f : H₀)),
          FunctionalInequalities.Analysis.Semigroup.Generated.preserves_form_domain T hT hd (v n) ht⟩‖ := by
        rw [hq_sub n]
      _ ≤ ‖T (v n)‖ :=
        FunctionalInequalities.Analysis.Semigroup.Generated.norm_map_apply_le T hT hd (v n) ht
          (FunctionalInequalities.Analysis.Semigroup.Generated.preserves_form_domain T hT hd (v n) ht)

  have hsub :
      Tendsto
        (fun n => T ⟨u n, (hu n).2⟩ - T f)
        atTop (𝓝 (T f - T f)) := by
    have hconst :
        Tendsto (fun _ : ℕ => T f) atTop (𝓝 (T f)) :=
      tendsto_const_nhds
    exact hu₂.sub hconst

  have hv_tendsto :
      Tendsto (fun n => T (v n)) atTop (𝓝 0) := by
    have h := hsub
    simpa only [hmap_sub, sub_self] using h

  have hv_norm :
      Tendsto (fun n => ‖T (v n)‖) atTop (𝓝 0) := by
    simpa using hv_tendsto.norm

  have hdiff_norm :
      Tendsto (fun n => ‖T (q n) - T q₀‖) atTop (𝓝 0) := by
    apply
      tendsto_of_tendsto_of_tendsto_of_le_of_le'
        tendsto_const_nhds hv_norm
    · filter_upwards with n
      exact norm_nonneg _
    · exact Filter.Eventually.of_forall hbound

  have hdiff :
      Tendsto (fun n => T (q n) - T q₀) atTop (𝓝 0) :=
    (tendsto_zero_iff_norm_tendsto_zero).2 hdiff_norm

  have hq :
      Tendsto (fun n => T (q n)) atTop (𝓝 (T q₀)) := by
    have hconst :
        Tendsto (fun _ : ℕ => T q₀) atTop (𝓝 (T q₀)) :=
      tendsto_const_nhds
    have h := hdiff.add hconst
    simpa only [sub_add_cancel, zero_add] using h

  have hleft :
      Tendsto (fun n => ‖T (q n)‖ ^ 2) atTop (𝓝 (‖T q₀‖ ^ 2)) := by
    simpa using hq.norm.pow 2

  have hright :
      Tendsto
        (fun n => Real.exp (-2 * ρ * t) *
          ‖T ⟨u n, (hu n).2⟩‖ ^ 2)
        atTop
        (𝓝 (Real.exp (-2 * ρ * t) * ‖T f‖ ^ 2)) := by
    have hnorm :
        Tendsto (fun n => ‖T ⟨u n, (hu n).2⟩‖ ^ 2) atTop
          (𝓝 (‖T f‖ ^ 2)) := by
      simpa using hu₂.norm.pow 2
    simpa using tendsto_const_nhds.mul hnorm

  have hle : ∀ n,
      ‖T (q n)‖ ^ 2 ≤
        Real.exp (-2 * ρ * t) * ‖T ⟨u n, (hu n).2⟩‖ ^ 2 := by
    intro n
    simpa [q] using
      (FunctionalInequalities.Analysis.Semigroup.Generated.norm_map_apply_sq_le_exp_of_mem_adjointComp_readable
        T hT hd hcurv ⟨u n, hu n⟩ ht)

  have hlimit :
      ‖T q₀‖ ^ 2 ≤ Real.exp (-2 * ρ * t) * ‖T f‖ ^ 2 := by
    exact
      tendsto_le_of_eventuallyLE hleft hright
        (Filter.Eventually.of_forall hle)

  simpa [q₀] using hlimit
