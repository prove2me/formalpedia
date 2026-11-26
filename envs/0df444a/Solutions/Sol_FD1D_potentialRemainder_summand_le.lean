-- Prove2me | solution 1 for FD1D.potentialRemainder_summand_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:05:43.752608+00:00
-- url     : https://prove2.me/submissions/3bdf3e4f-532d-49ce-8d85-2cd03fb056ec

import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_Drift
import Definitions.Def_FD1D_Potential
import Theorems.Thm_FD1D_node_remainder_le


set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators
namespace FD1D
theorem _root_.solution
    {a N q h p : ℝ}
    (hp : 0 ≤ p) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (haN : 0 < N + a) (hmajor : p ≤ (N + a) * h) :
    p ^ 3 * (1 - q) / ((N + a) * (N + a + 1)) ≤ p * h ^ 2 :=
  (node_remainder_le hp hq0 hq1 haN hmajor).2
end FD1D
