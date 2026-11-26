-- Prove2me | solution 1 for FD1D.main_horizon_long_enough
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:56:38.113313+00:00
-- url     : https://prove2.me/submissions/06ad672c-52e7-464b-ad99-8a7dba81dd35

import Definitions.Def_FD1D_Arithmetic
import Definitions.Def_FD1D_Drift

set_option autoImplicit true
open FD1D
noncomputable section
namespace FD1D
theorem _root_.solution {m N : ℕ} (hm : 1 ≤ m)
    (hN : 2 * m ^ 2 ≤ N) : m ^ 2 ≤ N - m := by
  have hmm : m ≤ m ^ 2 := by
    nlinarith [Nat.mul_le_mul_left m hm]
  omega
end FD1D
