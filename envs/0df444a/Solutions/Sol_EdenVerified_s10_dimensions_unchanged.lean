-- Prove2me | solution 1 for EdenVerified.s10_dimensions_unchanged
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:59:29.675042+00:00
-- url     : https://prove2.me/submissions/6b478927-fd6c-488e-a69b-7136ec91a377

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_frequencyAsymptoticDimension_eq
import Theorems.Thm_Eden_frequencyFiniteTimeDimension_eq
import Theorems.Thm_Eden_frequencyGlobalLyapunovDimension_eq
import Theorems.Thm_Eden_frequencyLyapunovExponent_eq
import Theorems.Thm_Eden_tendsto_frequencyLyapunovExponent


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution (c ν : ℝ) :
    (∀ t : ℝ, 0 ≤ t → ∀ p : PhaseSpace,
      frequencyFiniteTimeDimension c ν t p = finiteTimeDimension c t p) ∧
    (∀ K : Set PhaseSpace,
      frequencyGlobalLyapunovDimension c ν K = globalLyapunovDimension c K) ∧
    (∀ p : PhaseSpace, ∀ i : Fin 5,
      frequencyLyapunovExponent c ν p i = lyapunovExponent c p i ∧
      Tendsto (fun t : ℝ => Real.log
        ((fderiv ℝ (frequencyEvolution c ν t) p).toLinearMap.singularValues i) / t)
        atTop (𝓝 (frequencyLyapunovExponent c ν p i))) ∧
    (∀ p : PhaseSpace, frequencyAsymptoticDimension c ν p = asymptoticDimension c p) :=
  ⟨fun t ht p => frequencyFiniteTimeDimension_eq c ν ht p,
    frequencyGlobalLyapunovDimension_eq c ν,
    fun p i => ⟨frequencyLyapunovExponent_eq c ν p i, tendsto_frequencyLyapunovExponent c ν p i⟩,
    frequencyAsymptoticDimension_eq c ν⟩
end EdenVerified
