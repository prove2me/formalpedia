-- Prove2me | solution 1 for EdenVerified.p25_mem_positiveReturnSet_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:17:30.02647+00:00
-- url     : https://prove2.me/submissions/c12ac5b9-872e-4740-8175-e8aefb94609e

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_mem_positiveReturnSet_iff


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {c : ℝ} (hc : 0 < c) (p : PhaseSpace),
    p ∈ positiveReturnSet c ↔ p = 0 ∨ p ∈ firstCircle 1 ∨ p ∈ firstCircle 2 ∨
      p ∈ secondCircle 1 ∨ p ∈ secondCircle 2 :=
  @Eden.mem_positiveReturnSet_iff
end EdenVerified
