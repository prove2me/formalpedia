-- Prove2me | solution 1 for EdenVerified.s10_radial_and_singular_values
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:59:18.746272+00:00
-- url     : https://prove2.me/submissions/11ee59d3-6496-41f3-8b7d-f002c6e66691

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_fderiv_frequencyEvolution_bijective
import Theorems.Thm_Eden_frequencyEvolution_fifth
import Theorems.Thm_Eden_radiusSq_frequencyEvolution
import Theorems.Thm_Eden_singularValues_fderiv_frequencyEvolution
import Theorems.Thm_Eden_singularValues_frequencyEvolution_eq


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution (c ν : ℝ) (t : ℝ) (ht : 0 ≤ t) (p : PhaseSpace) :
    radiusSq₁ (frequencyEvolution c ν t p) = squaredRadiusEvolution t (radiusSq₁ p) ∧
    radiusSq₂ (frequencyEvolution c ν t p) = squaredRadiusEvolution t (radiusSq₂ p) ∧
    frequencyEvolution c ν t p 4 = Real.exp (-c*t)*p 4 ∧
    (fderiv ℝ (frequencyEvolution c ν t) p).toLinearMap.singularValues =
      (fderiv ℝ (evolution c t) p).toLinearMap.singularValues ∧
    Finset.univ.val.map (fun i : Fin 5 =>
      (fderiv ℝ (frequencyEvolution c ν t) p).toLinearMap.singularValues i) =
      Finset.univ.val.map (fun i : Fin 5 => derivativeFactors c t p i) ∧
    Function.Bijective (fderiv ℝ (frequencyEvolution c ν t) p) :=
  ⟨(radiusSq_frequencyEvolution c ν ht p).1, (radiusSq_frequencyEvolution c ν ht p).2,
    frequencyEvolution_fifth c ν t p, singularValues_frequencyEvolution_eq c ν ht p,
    singularValues_fderiv_frequencyEvolution c ν ht p, fderiv_frequencyEvolution_bijective c ν ht p⟩
end EdenVerified
