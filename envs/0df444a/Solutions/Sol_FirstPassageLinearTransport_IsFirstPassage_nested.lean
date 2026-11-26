-- Prove2me | solution 1 for FirstPassageLinearTransport.IsFirstPassage.nested
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:30:26.696328+00:00
-- url     : https://prove2.me/submissions/4521b888-f567-41a5-8904-60e74bbe5a22

import Definitions.Def_FirstPassageLinearTransport_LossTransport
import Definitions.Def_FirstPassageLinearTransport_RawDynamics
import Definitions.Def_FirstPassageLinearTransport_NestedRecertification
import Theorems.Thm_FirstPassageLinearTransport_orbit_add


set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section
namespace FirstPassageLinearTransport
namespace IsFirstPassage
theorem _root_.solution
    {Ylo Yhi n t h : ℕ}
    (hthreshold : Ylo < Yhi)
    (hhi : IsFirstPassage Yhi n t)
    (hlo : IsFirstPassage Ylo (orbit t n) h) :
    IsFirstPassage Ylo n (t + h) := by
  constructor
  · calc
      orbit (t + h) n = orbit (h + t) n := by rw [Nat.add_comm]
      _ = orbit h (orbit t n) := orbit_add h t n
      _ ≤ Ylo := hlo.1
  · intro j hj
    by_cases hjt : j < t
    · exact hthreshold.trans (hhi.2 j hjt)
    · have htj : t ≤ j := by omega
      have hlocal : j - t < h := by omega
      have hjform : j = (j - t) + t := by omega
      rw [hjform, orbit_add]
      exact hlo.2 (j - t) hlocal
end IsFirstPassage
end FirstPassageLinearTransport
