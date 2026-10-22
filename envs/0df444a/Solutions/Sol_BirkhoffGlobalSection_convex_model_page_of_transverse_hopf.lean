-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_model_page_of_transverse_hopf
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-09-28T03:21:27.495687+00:00
-- url     : https://prove2.me/submissions/ae61087a-5901-40c5-8ca7-ed5876969b20
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BirkhoffGlobalSection_convex_model_flow_dynamically_convex
import Theorems.Thm_BirkhoffGlobalSection_transverse_hopf_isotopy_spans_elliptic_disk
import Theorems.Thm_BirkhoffGlobalSection_elliptic_disk_page_of_dynamical_convexity

open BirkhoffGlobalSection

set_option autoImplicit false

theorem solution {μ c : ℝ}
    (M : ConvexRegularizationModel μ c)
    (φ : Flow ℝ (LeftEnergyState μ c))
    (D : ConvexModelDynamics M φ) (γ : PeriodicOrbit φ)
    (Γ : PeriodicOrbit D.flow)
    (hsimple : IsSimplePeriodicOrbit D.flow Γ)
    (htrace : convexModelOrbitSet Γ = M.toModel '' orbitSet γ)
    (hsymmetric : ∀ y ∈ frontier M.body, -y ∈ frontier M.body)
    (hHopf : Nonempty (EquivariantTransverseHopfIsotopy
      (radialNormalize '' convexModelOrbitSet Γ))) :
    Nonempty (ConvexModelRationalPage M D γ) := by
  obtain ⟨I⟩ := hHopf
  obtain ⟨disk⟩ :=
    transverse_hopf_isotopy_spans_elliptic_disk _ I
  exact elliptic_disk_page_of_dynamical_convexity M φ D γ Γ hsimple htrace
    hsymmetric (convex_model_flow_dynamically_convex M) disk
