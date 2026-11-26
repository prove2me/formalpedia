-- Prove2me | solution 1 for FirstPassageLinearTransport.orbitMinimum_eq_orbit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:56:08.414921+00:00
-- url     : https://prove2.me/submissions/f4324d06-6951-4c25-9bf1-bc010e3c99f9

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Lattice.Nat
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.Instances.Nat
import Definitions.Def_FirstPassageLinearTransport_Basic

set_option autoImplicit true
open FirstPassageLinearTransport
namespace FirstPassageLinearTransport
theorem _root_.solution (n : ℕ) :
    ∃ k : ℕ, orbitMinimum n = orbit k n := by
  obtain ⟨k, hk⟩ :=
    Nat.sInf_mem (Set.range_nonempty fun k : ℕ => orbit k n)
  exact ⟨k, by simpa [orbitMinimum] using hk.symm⟩
end FirstPassageLinearTransport
