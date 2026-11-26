-- Prove2me | solution 1 for FirstPassageLinearTransport.eventually_interval_rankTransport_small
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:40:12.289462+00:00
-- url     : https://prove2.me/submissions/b6c15471-ef82-491b-8bab-c90dab198f3d

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_FirstPassageLinearTransport_TerminalProfile
import Definitions.Def_FirstPassageLinearTransport_RankTransportAsymptotics
import Theorems.Thm_FirstPassageLinearTransport_eventually_rankTransport_small

set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {r : ℚ} (hr : 0 < r) :
    ∀ᶠ L : ℕ in atTop, ∀ U q : ℕ, q ∈ Finset.Icc L U →
      ((((q + 2 : ℕ) : ℚ) / r) / ((2 ^ q : ℕ) : ℚ)) ≤ 1 / 3 := by
  have hbase := eventually_rankTransport_small hr
  rw [eventually_atTop] at hbase ⊢
  obtain ⟨q₀, hq₀⟩ := hbase
  refine ⟨q₀, ?_⟩
  intro L hL U q hq
  exact hq₀ q (hL.trans (Finset.mem_Icc.mp hq).1)
end FirstPassageLinearTransport
