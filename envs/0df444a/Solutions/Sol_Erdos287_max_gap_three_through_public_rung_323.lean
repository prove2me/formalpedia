-- Prove2me | solution 1 for Erdos287.max_gap_three_through_public_rung_323
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T22:59:02.312282+00:00
-- url     : https://prove2.me/submissions/6211da01-f078-4ff9-b49e-20c8cfa79a9d

import Theorems.Thm_Erdos287_max_gap_three_through_main3_endpoint
import Theorems.Thm_Erdos287_first_three_reconstructed_rungs
import Theorems.Thm_Erdos287_gap_three_in_public_certificate_rungs_4_through_67
import Theorems.Thm_Erdos287_gap_three_in_public_certificate_rungs_68_through_323

set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

theorem solution (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hbound : f (k - 1) ≤ 7208116319200367450407115533588980011400784121272241099449580028658628209152193060371635799711480110024882516743560588651098146444954442114294176237768388665061338446562753736262843608661830460545436394411515307479615712118070190680809270944500958312921705785003119324582869277805117435) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by
  by_cases h0 : f (k - 1) ≤ 381185219244960776204622798194589878857417272332616682539469868641615417785666328820964948335432532885427126626573411739149117629379557737669727589422795325435
  · exact Erdos287.max_gap_three_through_main3_endpoint k hk f hf1 hmono hsum h0
  push_neg at h0
  by_cases h1 : f (k - 1) ≤ 5887104692222610115311068713886416666636503914806049781997679266319785399143980188838070510421047673741709770480679026139361407216193271418506778065818374635530
  · exact Erdos287.first_three_reconstructed_rungs k hk f hf1 hmono hsum (by omega) h1
  push_neg at h1
  by_cases h2 : f (k - 1) ≤ 127121066678798445735243883196317776949351426878578394099564929136550843411572772149955019782860736757937532214437526600769419124790518099200969633104128306711796545988048739553341603835
  · exact Erdos287.gap_three_in_public_certificate_rungs_4_through_67 k hk f hf1 hmono hsum (by omega) h2
  push_neg at h2
  exact Erdos287.gap_three_in_public_certificate_rungs_68_through_323 k hk f hf1 hmono hsum (by omega) hbound

