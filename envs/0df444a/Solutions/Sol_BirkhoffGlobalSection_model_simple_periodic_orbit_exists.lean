-- Prove2me | solution 1 for BirkhoffGlobalSection.model_simple_periodic_orbit_exists
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-30T16:31:20.175987+00:00
-- url     : https://prove2.me/submissions/a7875d32-7d8b-43f1-abae-557c6c9e8327

import Definitions.Def_BirkhoffGlobalSection_ConvexModelDynamics

open BirkhoffGlobalSection

/-- Increasing complete trajectory clocks preserve prime periodic orbits and
their geometric images. No binding-page existence is assumed. -/
theorem solution {μ c : ℝ} (M : ConvexRegularizationModel μ c)
    (φ : Flow ℝ (LeftEnergyState μ c)) (D : ConvexModelDynamics M φ)
    (γ : PeriodicOrbit φ) (hγ : IsSimplePeriodicOrbit φ γ) :
    ∃ δ : PeriodicOrbit D.flow,
      δ.point = M.mapState γ.point ∧
      δ.period = D.clock γ.point γ.period ∧
      IsSimplePeriodicOrbit D.flow δ ∧
      Set.range (fun t : ℝ => ((D.flow t δ.point : ConvexModelState M) : Phase)) =
        M.toModel '' orbitSet γ := by
  have hpos : 0 < D.clock γ.point γ.period := by
    rw [← D.clock_zero γ.point]
    exact (D.clock γ.point).strictMono γ.period_pos
  have hclosed : D.flow (D.clock γ.point γ.period) (M.mapState γ.point) =
      M.mapState γ.point := by
    apply Subtype.ext
    rw [D.conjugacy, γ.closed]
    rfl
  let δ : PeriodicOrbit D.flow :=
    ⟨M.mapState γ.point, D.clock γ.point γ.period, hpos, hclosed⟩
  refine ⟨δ, rfl, rfl, ?_, ?_⟩
  · intro t ht htperiod hret
    let τ := (D.clock γ.point).symm t
    have hτpos : 0 < τ := by
      apply (D.clock γ.point).lt_symm_apply.mpr
      simpa only [D.clock_zero] using ht
    have hτperiod : τ < γ.period := by
      apply (D.clock γ.point).symm_apply_lt.mpr
      exact htperiod
    apply hγ τ hτpos hτperiod
    apply Subtype.ext
    have he : M.toModel ((φ τ γ.point : LeftEnergyState μ c) : Phase) =
        M.toModel (γ.point : Phase) := by
      rw [← D.conjugacy]
      change ((D.flow ((D.clock γ.point) ((D.clock γ.point).symm t))
        δ.point : ConvexModelState M) : Phase) = _
      rw [(D.clock γ.point).apply_symm_apply, hret]
      rfl
    calc
      ((φ τ γ.point : LeftEnergyState μ c) : Phase) =
          M.fromModel (M.toModel ((φ τ γ.point : LeftEnergyState μ c) : Phase)) :=
        (M.left_inverse _ (M.contains_component (φ τ γ.point).property)).symm
      _ = M.fromModel (M.toModel (γ.point : Phase)) := congrArg M.fromModel he
      _ = (γ.point : Phase) := M.left_inverse _ (M.contains_component γ.point.property)
  · apply Set.Subset.antisymm
    · rintro y ⟨t, rfl⟩
      refine ⟨((φ ((D.clock γ.point).symm t) γ.point : LeftEnergyState μ c) : Phase),
        ⟨(D.clock γ.point).symm t, rfl⟩, ?_⟩
      have he := D.conjugacy γ.point ((D.clock γ.point).symm t)
      simpa only [OrderIso.apply_symm_apply] using he.symm
    · rintro y ⟨s, ⟨t, rfl⟩, rfl⟩
      refine ⟨D.clock γ.point t, ?_⟩
      exact D.conjugacy γ.point t
