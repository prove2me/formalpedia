-- Prove2me | solution 3 for AvramDividend.Classical.avram_bvb_phys89b_zero_contact_original_BV_drift_only_budget_formal_negation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T18:05:51.182196+00:00
-- url     : https://prove2.me/submissions/464b9b7c-a0f2-411a-8be1-9bd3cf9d7d51

import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.Filter.Defs
import Definitions.Def_AvramDividend_Classical_BVZeroContactUniversalClaim
import Definitions.Def_AvramDividend_Classical_BVZeroContactUniversalClaimType0
import Definitions.Def_AvramDividend_Classical_BVUniverseRestrictPublic20261117
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
    (bvbUniverseRestrictPublic20261117 h)
