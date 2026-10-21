-- Prove2me | solution 1 for EvolvHier.SocialOpt.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T02:48:41.307495+00:00
-- url     : https://prove2.me/submissions/95943b02-6ffe-466e-8f08-527b66f2d178

import Mathlib
import Definitions.Def_EvolvHier_SocialOpt_Setting
import Theorems.Thm_EvolvHier_SocialOpt_step_4
import Theorems.Thm_EvolvHier_SocialOpt_step_5

open EvolvHier.SocialOpt

theorem solution (T : Technology) :
    IsDecSociallyOptimal T tStar ∧
      ∀ t, IsScheme t → IsDecSociallyOptimal T t → t = tStar :=
  ⟨step_4 T, step_5 T⟩
