-- Prove2me | solution 1 for GRH.fixed_rational_moebius_frequencies_escape_exceptional_square_cutoffs
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T06:09:41.206654+00:00
-- url     : https://prove2.me/submissions/1b14abd3-a7da-414c-9049-f4906e9bf6ba
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GRH_fixed_frequency_escape_iff_squarefull_denominator_tests
import Theorems.Thm_GRH_moebius_square_cutoff_power_bounds_at_squarefull_denominators

theorem solution :
    GRH.AdditiveMoebiusSpectrum.escapes := by
  exact GRH.fixed_frequency_escape_iff_squarefull_denominator_tests.mpr
    GRH.moebius_square_cutoff_power_bounds_at_squarefull_denominators
