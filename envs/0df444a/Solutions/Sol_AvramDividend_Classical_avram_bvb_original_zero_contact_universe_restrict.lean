-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_original_zero_contact_universe_restrict
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T18:05:27.871545+00:00
-- url     : https://prove2.me/submissions/83eb6d5a-a2e0-4f82-9980-a93ecdbe11c2

import Mathlib
import Definitions.Def_AvramDividend_Classical_BVZeroContactUniversalClaim
import Definitions.Def_AvramDividend_Classical_BVZeroContactUniversalClaimType0
import Definitions.Def_AvramDividend_Classical_BVUniverseRestrictPublic20261117
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open AvramDividend.Classical
universe u

theorem solution (h : BVZeroContactUniversalClaim.{u}) :
    BVZeroContactUniversalClaimType0 := by
  exact bvbUniverseRestrictPublic20261117 h
