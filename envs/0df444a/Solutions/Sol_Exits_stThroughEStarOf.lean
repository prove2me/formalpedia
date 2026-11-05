-- Prove2me | solution 1 for Exits.stThroughEStarOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:32:59.516385+00:00
-- url     : https://prove2.me/submissions/676d8d83-2e91-43ab-a51f-4897e333a574

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Exits_AlgDefs
import Definitions.Def_Eight_ViaGrouping_Count
import Definitions.Def_Eight_SecLevel_EStar
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_Exits_Decides
import Theorems.Thm_Eight_decidesInSteps_mono
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Paper_achievable_of_eStar_lt
import Theorems.Thm_Paper_steps_to_time


set_option autoImplicit false
section
section
open Exits
open Groundwork Groundwork.Prog Groundwork.Stepped Paper Eight Eight.SecNetworks Eight.ViaGrouping Suffices Enumerate
namespace Exits
theorem _root_.solution : StThroughEStarOf := by
  intro h0 hEn hP δ hδ
  -- «We may assume δ ≤ 1.» (The bound in steps is taken at δ/2.)
  have hd : 0 < min (δ / 2) 1 := lt_min (by positivity) one_pos
  -- «Let M = M(δ/3) and δ' = δ/(3M) ≤ 1/3.» (with min(δ/2, 1) in the place of δ)
  obtain ⟨M, τ, hM, hE⟩ := hEn (min (δ / 2) 1 / 3) (by positivity)
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hδ' : 0 < min (δ / 2) 1 / (3 * (M : ℝ)) := by positivity
  -- «Since e* = 0 < δ'/12 and achievability is monotone in e (Definition 4), (K, δ'/12) is
  -- achievable for infinitely many K. Fix such a K ≥ 72/δ' and put g = 3K⁸; …»
  have hstar : eStar < min (δ / 2) 1 / (3 * (M : ℝ)) / 12 := by rw [h0]; positivity
  obtain ⟨K, hK, E, hEk, hEw⟩ := achievable_of_eStar_lt hstar ⌈72 / (min (δ / 2) 1 / (3 * (M : ℝ)))⌉₊
  have hKδ : 72 / (min (δ / 2) 1 / (3 * (M : ℝ))) ≤ K := (Nat.le_ceil _).trans (by exact_mod_cast hK)
  -- «By Lemma 4 with ε = δ/3, it suffices …», the network of Φ, «Cost», «so the total time is
  -- O(2^{δn})»
  obtain ⟨p1, p2⟩ := hP (min (δ / 2) 1) M τ K E hd (min_le_right _ _) hM hE hKδ hEk hEw
  exact steps_to_time hδ _ p1 (decidesInSteps_mono p2 (min_le_left _ _))
end Exits
