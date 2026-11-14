-- Prove2me | solution 1 for CountingLLL.ContractedWalk.iid_tail_law
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:34:54.796243+00:00
-- url     : https://prove2.me/submissions/bbe60b9f-593f-4f5d-88cf-c24b6cc6da38

import Definitions.Def_CountingLLL_ContractedWalk

set_option autoImplicit false
open MeasureTheory ProbabilityTheory CountingLLL.ContractedWalk
open scoped ENNReal

private theorem bitLaw_probability' (p : ℝ≥0∞) (hp : p ≤ 1) : IsProbabilityMeasure (bitLaw p) := by
  constructor
  simp only [bitLaw, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  exact tsub_add_cancel_of_le hp

theorem solution (p : ℝ≥0∞) (hp : p ≤ 1) :
    (tapeLaw p).map (fun ω n => ω (n+1)) = tapeLaw p := by
  letI : IsProbabilityMeasure (bitLaw p) := bitLaw_probability' p hp
  exact Measure.map_infinitePi_infinitePi_of_inj (f := fun n : ℕ => n+1) (by intro a b h; exact Nat.add_right_cancel h)
