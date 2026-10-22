-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_model_periodic_orbit_transport
-- status  : ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-09-27T02:11:05.5322+00:00
-- url     : https://prove2.me/submissions/76062b66-6da3-479a-87d1-57201214b16a

import Definitions.Def_BirkhoffGlobalSection_TransverseHopf

open BirkhoffGlobalSection

set_option autoImplicit false

theorem solution {μ c : ℝ} (M : ConvexRegularizationModel μ c)
    (φ : Flow ℝ (LeftEnergyState μ c)) (D : ConvexModelDynamics M φ)
    (γ : PeriodicOrbit φ) (hsimple : IsSimplePeriodicOrbit φ γ) :
    IsSimplePeriodicOrbit D.flow (D.mapPeriodicOrbit γ) ∧
      convexModelOrbitSet (D.mapPeriodicOrbit γ) = M.toModel '' orbitSet γ := by
  constructor
  · intro t ht hperiod hclosed
    let s : ℝ := (D.clock γ.point).symm t
    have hclock : D.clock γ.point s = t := (D.clock γ.point).apply_symm_apply t
    have hspos : 0 < s := by
      apply (D.clock γ.point).lt_iff_lt.mp
      rw [D.clock_zero, hclock]
      exact ht
    have hsperiod : s < γ.period := by
      apply (D.clock γ.point).lt_iff_lt.mp
      rw [hclock]
      exact hperiod
    apply hsimple s hspos hsperiod
    apply M.stateHomeomorph.injective
    apply Subtype.ext
    change M.toModel ((φ s γ.point : LeftEnergyState μ c) : Phase) =
      M.toModel (γ.point : Phase)
    rw [← D.conjugacy γ.point s, hclock]
    exact congrArg Subtype.val hclosed
  · ext y
    constructor
    · rintro ⟨t, rfl⟩
      let s : ℝ := (D.clock γ.point).symm t
      refine ⟨((φ s γ.point : LeftEnergyState μ c) : Phase), ⟨s, rfl⟩, ?_⟩
      change M.toModel ((φ s γ.point : LeftEnergyState μ c) : Phase) =
        ((D.flow t (M.mapState γ.point) : ConvexModelState M) : Phase)
      rw [← D.conjugacy γ.point s]
      simp only [s, OrderIso.apply_symm_apply]
    · rintro ⟨x, ⟨t, rfl⟩, rfl⟩
      refine ⟨D.clock γ.point t, ?_⟩
      exact D.conjugacy γ.point t
