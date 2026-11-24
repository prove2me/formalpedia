-- Prove2me | solution 1 for Formalism.GaloisIrreducibility.block_bound_of_orbits
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:58:39.363177+00:00
-- url     : https://prove2.me/submissions/90f18046-17c3-434d-bb61-b1e4afaf43a6

import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableOf
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_BlockBoundOfOrbits

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GaloisIrreducibility
namespace Formalism.GaloisIrreducibility
theorem _root_.solution : BBOf := by
  intro hF g d S hg hd hS hB
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  have hgd : 2 ≤ g ^ d := le_trans hg (Nat.le_self_pow (by omega) g)
  have hn : 1 ≤ g ^ d - 1 := by omega
  have hg1 : (1 : ℝ) < g := by exact_mod_cast hg
  have hpos : (0 : ℝ) < (g : ℝ) ^ ((d : ℝ) / 4) := Real.rpow_pos_of_pos (by linarith) _
  have key := hF (g ^ d - 1) _ S hn hpos hS hne hB
  have h2 : ((g ^ d - 1 : ℕ) : ℝ) < (g : ℝ) ^ (d : ℝ) := by
    rw [Real.rpow_natCast, Nat.cast_sub (by omega)]; push_cast; linarith
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)] at key
  have h3 : (d : ℝ) / 4 * S.card < d := (Real.rpow_lt_rpow_left_iff hg1).mp (key.trans h2)
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have : (S.card : ℝ) < 4 := by nlinarith
  have : S.card < 4 := by exact_mod_cast this
  omega
end Formalism.GaloisIrreducibility
