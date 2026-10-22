-- Prove2me | solution 1 for BirkhoffGlobalSection.left_energy_component_equivariant_sphere
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T17:48:11.614254+00:00
-- url     : https://prove2.me/submissions/b4a24b4d-5cfe-45ff-955b-61eeefcd5f0c

import Mathlib.Topology.Homeomorph.Lemmas
import Theorems.Thm_BirkhoffGlobalSection_left_energy_component_compact
import Theorems.Thm_BirkhoffGlobalSection_left_energy_component_radial_bijection

open BirkhoffGlobalSection

theorem solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∃ e : LeftEnergyState μ c ≃ₜ {x : Phase // x ∈ unitThreeSphere},
      IsAntipodallyEquivariantSphereHomeomorph e := by
  obtain ⟨f, hcont, hbij, hrad⟩ :=
    left_energy_component_radial_bijection μ c hμ0 hμ1 hc
  letI : CompactSpace (LeftEnergyState μ c) :=
    isCompact_iff_compactSpace.mp
      (left_energy_component_compact μ c hμ0 hμ1 hc)
  have hfhomeo : IsHomeomorph f :=
    isHomeomorph_iff_continuous_bijective.mpr ⟨hcont, hbij⟩
  let e : LeftEnergyState μ c ≃ₜ {x : Phase // x ∈ unitThreeSphere} :=
    hfhomeo.homeomorph f
  refine ⟨e, ?_⟩
  intro s₁ s₂ hs
  change (f s₂ : Phase) = -(f s₁ : Phase)
  rw [hrad s₂, hrad s₁]
  ext i
  simp [hs, zNormSq, wNormSq, neg_div]
