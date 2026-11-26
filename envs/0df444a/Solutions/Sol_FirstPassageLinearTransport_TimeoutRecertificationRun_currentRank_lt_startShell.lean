-- Prove2me | solution 1 for FirstPassageLinearTransport.TimeoutRecertificationRun.currentRank_lt_startShell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:18:16.748037+00:00
-- url     : https://prove2.me/submissions/60ddcf5e-b8dc-4031-943b-0aa8f6387aa7

import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointAsymptotics
import Definitions.Def_FirstPassageLinearTransport_AsymptoticBounds
import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_TimeoutOrbitCeiling
import Theorems.Thm_FirstPassageLinearTransport_rationalTargetRank_lt_parent


set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
namespace TimeoutRecertificationRun
theorem _root_.solution
    {P : TimeoutHighRunData} {K₀ : ℝ}
    {L M S n elapsed q : ℕ}
    (hrun : TimeoutRecertificationRun P K₀ L M S n elapsed q) : q < M := by
  induction hrun with
  | first hSM hM0 hnShell hnGood =>
      have hMpos : 0 < M := by
        have ht := P.pHi.target_one_lt M hM0
        by_contra hM
        have hMzero : M = 0 := Nat.eq_zero_of_not_pos hM
        rw [hMzero] at ht
        norm_num [targetScale] at ht
      exact rationalTargetRank_lt_parent
        (by exact_mod_cast P.pHi.r_pos.le)
        (by exact_mod_cast P.pHi.r_lt_one) hMpos
  | nextHi hrun hSm hm0 hmPrev hsourceShell hsourceGood hgap ih =>
      exact hgap.trans ih
  | nextLo hrun hmS hLm hmPrevLo hmPrevHi hsourceShell hpass hqpos
      hqparent hgap ih =>
      exact hgap.trans ih
end TimeoutRecertificationRun
end FirstPassageLinearTransport
