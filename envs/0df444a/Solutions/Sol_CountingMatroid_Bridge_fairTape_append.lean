-- Prove2me | solution 1 for CountingMatroid.Bridge.fairTape_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T19:28:48.512066+00:00
-- url     : https://prove2.me/submissions/796db88b-6f68-48b9-b90e-1a6f025734d4

import Mathlib
import Definitions.Def_CountingMatroid_Model_Run
import Definitions.Def_CommonBasesFPRAS
import Definitions.Def_CountingMatroid_Bridge_Presampling

set_option autoImplicit false
set_option maxHeartbeats 800000

open CountingMatroid CountingMatroid.Model CountingMatroid.Model.Run CountingMatroid.Model.Operations
open CountingMatroid.Bridge

/-- Concatenating independent fair tapes gives one fair tape. -/
theorem solution (a b : ℕ) :
    (fairTape a).bind (fun xs => (fairTape b).map (xs ++ ·)) = fairTape (a + b) := by
  induction a with
  | zero =>
      simp only [fairTape, Nat.zero_add]
      change (PMF.pure ([] : List Bool)).bind
        (fun xs => (fairTape b).map (xs ++ ·)) = fairTape b
      rw [PMF.pure_bind]
      exact PMF.map_id _
  | succ a ih =>
      change (fairBitLaw.bind (fun bit => (fairTape a).map (List.cons bit))).bind
        (fun xs => (fairTape b).map (xs ++ ·)) = fairTape (a + 1 + b)
      rw [show a + 1 + b = (a + b) + 1 by omega]
      change _ = fairBitLaw.bind (fun bit => (fairTape (a + b)).map (List.cons bit))
      rw [PMF.bind_bind]
      congr 1
      funext bit
      rw [PMF.bind_map, ← ih, PMF.map_bind]
      congr 1
      funext xs
      rw [PMF.map_comp]
      rfl
