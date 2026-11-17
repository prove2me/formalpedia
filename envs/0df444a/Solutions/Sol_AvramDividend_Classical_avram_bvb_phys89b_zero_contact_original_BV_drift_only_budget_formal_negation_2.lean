-- Prove2me | solution 2 for AvramDividend.Classical.avram_bvb_phys89b_zero_contact_original_BV_drift_only_budget_formal_negation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T17:38:04.683505+00:00
-- url     : https://prove2.me/submissions/8ad082f9-6892-4101-9b88-a259d1c45206
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.Filter.Defs
import Definitions.Def_AvramDividend_Classical_BVZeroContactUniversalClaim
import Definitions.Def_AvramDividend_Classical_BVZeroContactUniversalClaimType0
import Theorems.Thm_AvramDividend_Classical_avram_bvb_original_zero_contact_universe_restrict
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys89b_original_zero_contact_drift_only_budget_type0_is_false
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem solution : ¬ BVZeroContactUniversalClaim := by
  change ¬ BVZeroContactUniversalClaim
  intro h
  exact avram_bvb_phys89b_original_zero_contact_drift_only_budget_type0_is_false
    (avram_bvb_original_zero_contact_universe_restrict h)
