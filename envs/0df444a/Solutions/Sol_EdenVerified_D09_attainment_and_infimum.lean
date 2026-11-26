-- Prove2me | solution 1 for EdenVerified.D09_attainment_and_infimum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:02:11.490025+00:00
-- url     : https://prove2.me/submissions/0565ebe7-7889-4cf9-957d-65d389f8db48

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_admissibleDimensions_nonempty
import Theorems.Thm_Eden_fderiv_evolution_bijective
import Theorems.Thm_Eden_finiteTimeDimension_isGreatest
import Theorems.Thm_Eden_isCompact_admissibleDimensions


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution (c : ℝ) (t : ℝ) (ht : 0 ≤ t)
    (p : PhaseSpace) (K : Set PhaseSpace) :
    {d : ℝ | d ∈ Icc 0 5 ∧
      1 ≤ singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap d}.Nonempty ∧
    IsCompact {d : ℝ | d ∈ Icc 0 5 ∧
      1 ≤ singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap d} ∧
    IsGreatest {d : ℝ | d ∈ Icc 0 5 ∧
      1 ≤ singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap d}
      (finiteTimeDimension c t p) ∧
    globalLyapunovDimension c K =
      sInf {v : ℝ | ∃ τ : ℝ, 0 < τ ∧ v = sSup (finiteTimeDimension c τ '' K)} :=
  ⟨admissibleDimensions_nonempty _,
    isCompact_admissibleDimensions (fderiv_evolution_bijective c ht p).injective,
    finiteTimeDimension_isGreatest c ht p, rfl⟩
end EdenVerified
