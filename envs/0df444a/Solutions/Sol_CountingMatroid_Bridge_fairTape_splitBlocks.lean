-- Prove2me | solution 1 for CountingMatroid.Bridge.fairTape_splitBlocks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T19:32:02.649816+00:00
-- url     : https://prove2.me/submissions/f78b9e0b-30d9-48c0-953f-4a15bcffa0e1

import Mathlib
import Definitions.Def_CountingMatroid_Model_Run
import Definitions.Def_CommonBasesFPRAS
import Definitions.Def_CountingMatroid_Bridge_Presampling
import Theorems.Thm_CountingMatroid_Analysis_SingleRunAccuracy_fairTape_support_iff_length
import Theorems.Thm_CountingMatroid_Bridge_fairTape_append

set_option autoImplicit false
set_option maxHeartbeats 800000

open CountingMatroid CountingMatroid.Model CountingMatroid.Model.Run CountingMatroid.Model.Operations
open CountingMatroid.Bridge

namespace CountingMatroid.Bridge

private theorem bind_congr_support {α β : Type} (p : PMF α) (f g : α → PMF β)
    (h : ∀ a ∈ p.support, f a = g a) : p.bind f = p.bind g := by
  apply PMF.ext
  intro b
  simp only [PMF.bind_apply]
  apply tsum_congr
  intro a
  by_cases ha : a ∈ p.support
  · rw [h a ha]
  · have hz : p a = 0 := by simpa [PMF.mem_support_iff] using ha
    simp [hz]

end CountingMatroid.Bridge

/-- Splitting one fair tape gives exactly the independent block law. -/
theorem solution (m width : ℕ) :
    (fairTape (m * width)).map (splitBlocks width m) = fairBlocks m width := by
  induction m with
  | zero =>
      simp only [Nat.zero_mul, fairTape, fairBlocks]
      change (PMF.pure ([] : List Bool)).map (splitBlocks width 0) = PMF.pure []
      exact PMF.pure_map _ _
  | succ m ih =>
      rw [Nat.succ_mul, Nat.add_comm (m * width) width, ← fairTape_append]
      rw [PMF.map_bind]
      change _ = (fairTape width).bind (fun block =>
        (fairBlocks m width).map (List.cons block))
      apply bind_congr_support
      intro block hblock
      have hlen := (Analysis.SingleRunAccuracy.fairTape_support_iff_length width block).mp hblock
      rw [PMF.map_comp, ← ih, PMF.map_comp]
      congr 1
      funext rest
      simp [splitBlocks, ← hlen]
