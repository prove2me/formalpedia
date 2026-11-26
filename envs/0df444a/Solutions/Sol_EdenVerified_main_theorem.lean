-- Prove2me | solution 1 for EdenVerified.main_theorem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:11:38.479954+00:00
-- url     : https://prove2.me/submissions/23ba85e0-81db-4781-b454-4c6ac005dca4

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_asymptoticDimension_attractor_isGreatest
import Theorems.Thm_Eden_asymptoticDimension_eq_target_iff
import Theorems.Thm_Eden_asymptoticDimension_periodic_isGreatest
import Theorems.Thm_Eden_attractor_isGlobalAttractor
import Theorems.Thm_Eden_contDiff_evolution
import Theorems.Thm_Eden_divergence_eq
import Theorems.Thm_Eden_divergence_le
import Theorems.Thm_Eden_evolution_add
import Theorems.Thm_Eden_evolution_torusPoint
import Theorems.Thm_Eden_evolution_unique
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_fderiv_evolution_bijective
import Theorems.Thm_Eden_finiteTimeDimension_attractor_isGreatest
import Theorems.Thm_Eden_finiteTimeDimension_eq_target_iff
import Theorems.Thm_Eden_finiteTimeDimension_periodic_isGreatest
import Theorems.Thm_Eden_globalLyapunovDimension_attractor
import Theorems.Thm_Eden_hasDerivAt_evolution
import Theorems.Thm_Eden_targetDimension_bounds
import Theorems.Thm_Eden_tendsto_finiteTimeDimension
import Theorems.Thm_Eden_tendsto_lyapunovExponent
import Theorems.Thm_Eden_torus_invariant_all_real
import Theorems.Thm_Eden_torus_no_positive_return
import Theorems.Thm_Eden_torus_subset_attractor
attribute [local simp] Eden.evolution_zero_time



set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution (c : ℝ) (hc : 4 < c) :
    (∀ p : PhaseSpace, evolution c 0 p = p ∧
      ∀ t : ℝ, 0 ≤ t → HasDerivAt (fun τ => evolution c τ p)
        (vectorField c (evolution c t p)) t) ∧
    (∀ (p : PhaseSpace) (f : ℝ → PhaseSpace),
      ContinuousOn f (Ici 0) →
      (∀ t : ℝ, 0 ≤ t → HasDerivWithinAt f (vectorField c (f t)) (Ici t) t) →
      f 0 = p → EqOn f (fun t => evolution c t p) (Ici 0)) ∧
    (∀ (s t : ℝ), 0 ≤ s → 0 ≤ t → ∀ p : PhaseSpace,
      evolution c (s + t) p = evolution c t (evolution c s p)) ∧
    (∀ t : ℝ, 0 ≤ t → ContDiff ℝ 1 (evolution c t)) ∧
    (∀ t : ℝ, 0 ≤ t → ∀ p : PhaseSpace,
      Function.Bijective (fderiv ℝ (evolution c t) p)) ∧
    IsGlobalAttractor c attractor ∧
    (∀ p : PhaseSpace,
      divergence c p = 4 - c - 6 * (radiusSq₁ p - 1) ^ 2 -
        6 * (radiusSq₂ p - 1) ^ 2 ∧ divergence c p ≤ 4 - c ∧ 4 - c < 0) ∧
    (4 < 4 + 4 / c ∧ 4 + 4 / c < 5) ∧
    (∀ t : ℝ, 0 < t →
      IsGreatest (finiteTimeDimension c t '' attractor) (4 + 4 / c) ∧
      {p ∈ attractor | finiteTimeDimension c t p = 4 + 4 / c} = torus) ∧
    (∀ p ∈ attractor, ∀ i : Fin 5,
      Tendsto (fun t : ℝ => Real.log
        ((fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) / t)
        atTop (𝓝 (lyapunovExponent c p i))) ∧
    (globalLyapunovDimension c attractor = 4 + 4 / c) ∧
    IsGreatest (asymptoticDimension c '' attractor) (4 + 4 / c) ∧
    ({p ∈ attractor | asymptoticDimension c p = 4 + 4 / c} = torus) ∧
    IsGreatest (asymptoticDimension c '' periodicEquilibriumSet c) 3 ∧
    (∀ t : ℝ, 0 < t →
      IsGreatest (finiteTimeDimension c t '' periodicEquilibriumSet c) 3) ∧
    (∀ (t : ℝ) (p : PhaseSpace), p ∈ torus → evolution c t p ∈ torus) ∧
    (∀ p ∈ torus, ∀ t : ℝ, 0 < t → evolution c t p ≠ p) ∧
    (∀ t θ₁ θ₂ : ℝ, evolution c t (torusPoint θ₁ θ₂) =
      torusPoint (θ₁ + t) (θ₂ + Real.sqrt 2 * t)) ∧
    (∀ p ∈ attractor, Tendsto (fun t : ℝ => finiteTimeDimension c t p)
      atTop (𝓝 (asymptoticDimension c p))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, attractor_isGlobalAttractor (by linarith), ?_,
    targetDimension_bounds hc, ?_, ?_, globalLyapunovDimension_attractor hc,
    asymptoticDimension_attractor_isGreatest hc, ?_,
    asymptoticDimension_periodic_isGreatest hc, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun p => ⟨evolution_zero_time c p, fun t ht => hasDerivAt_evolution c ht p⟩
  · exact fun p f hf hf' h0 => evolution_unique c p hf hf' h0
  · exact fun s t hs ht p => evolution_add c hs ht p
  · exact fun t ht => contDiff_evolution c ht 1
  · exact fun t ht p => fderiv_evolution_bijective c ht p
  · exact fun p => ⟨divergence_eq c p, divergence_le c p, by linarith⟩
  · intro t ht
    refine ⟨finiteTimeDimension_attractor_isGreatest hc ht, ?_⟩
    ext p
    constructor
    · exact fun hp => (finiteTimeDimension_eq_target_iff hc ht hp.1).mp hp.2
    · exact fun hp => ⟨torus_subset_attractor hp,
        (finiteTimeDimension_eq_target_iff hc ht (torus_subset_attractor hp)).mpr hp⟩
  · exact fun p _ i => tendsto_lyapunovExponent c p i
  · ext p
    constructor
    · exact fun hp => (asymptoticDimension_eq_target_iff hc hp.1).mp hp.2
    · exact fun hp => ⟨torus_subset_attractor hp,
        (asymptoticDimension_eq_target_iff hc (torus_subset_attractor hp)).mpr hp⟩
  · exact fun t ht => finiteTimeDimension_periodic_isGreatest hc ht
  · exact fun t p hp => torus_invariant_all_real c t hp
  · exact fun p hp t ht => torus_no_positive_return c hp ht
  · exact evolution_torusPoint c
  · exact fun p hp => tendsto_finiteTimeDimension hc hp
end EdenVerified
