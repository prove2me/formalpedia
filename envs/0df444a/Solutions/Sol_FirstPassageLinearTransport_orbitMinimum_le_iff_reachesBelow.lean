-- Prove2me | solution 1 for FirstPassageLinearTransport.orbitMinimum_le_iff_reachesBelow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:56:53.630853+00:00
-- url     : https://prove2.me/submissions/bea3aa3a-1ac6-46db-85d6-56723b28bc46

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Lattice.Nat
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.Instances.Nat
import Definitions.Def_FirstPassageLinearTransport_Basic
import Theorems.Thm_FirstPassageLinearTransport_orbitMinimum_eq_orbit

set_option autoImplicit true
open FirstPassageLinearTransport
namespace FirstPassageLinearTransport
theorem _root_.solution {n : ℕ} {Y : ℝ} :
    (orbitMinimum n : ℝ) ≤ Y ↔ ReachesBelow n Y := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := orbitMinimum_eq_orbit n
    exact ⟨k, by simpa [hk] using h⟩
  · rintro ⟨k, hk⟩
    calc
      (orbitMinimum n : ℝ) ≤ orbit k n := by
        exact_mod_cast Nat.sInf_le (Set.mem_range_self k)
      _ ≤ Y := hk
end FirstPassageLinearTransport
