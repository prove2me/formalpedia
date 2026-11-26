-- Prove2me | solution 1 for EdenVerified.D10_finite_time_convention
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:02:53.209872+00:00
-- url     : https://prove2.me/submissions/680fa584-c7c1-4b57-a482-6e15122b3998

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_admissibleDimensions_evolution_eq
import Theorems.Thm_Eden_finiteTimeDimension_eq_kaplanYorke


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution (c : ℝ) (t : ℝ) (ht : 0 < t)
    (p : PhaseSpace) :
    {d : ℝ | d ∈ Icc 0 5 ∧
      1 ≤ singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap d} =
      Icc 0 (kaplanYorkeDimension (normalizedLogSingularValues c t p)) ∧
    finiteTimeDimension c t p =
      kaplanYorkeDimension (normalizedLogSingularValues c t p) :=
  ⟨admissibleDimensions_evolution_eq c ht p, finiteTimeDimension_eq_kaplanYorke c ht p⟩
end EdenVerified
