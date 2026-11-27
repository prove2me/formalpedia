-- Prove2me | solution 1 for GRH.cofinal_lower_bound_for_completely_split_primes_at_squares
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T02:28:04.440635+00:00
-- url     : https://prove2.me/submissions/131b8ec4-ec2d-4f4b-af32-9e7fd94edec7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GRH_centered_moebius_iff_summable_one_class_prime_deficits_at_factorial_levels
import Theorems.Thm_GRH_cofinal_summability_of_positive_split_prime_deficits

theorem solution : GRH.SplitPrimeLower.cofinalPrimeLower :=
  GRH.centered_moebius_iff_summable_one_class_prime_deficits_at_factorial_levels.2.1.mpr
    GRH.cofinal_summability_of_positive_split_prime_deficits
