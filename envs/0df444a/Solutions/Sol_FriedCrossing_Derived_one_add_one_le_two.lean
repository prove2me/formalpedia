-- Prove2me | solution 1 for FriedCrossing.Derived.one_add_one_le_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:41:04.293622+00:00
-- url     : https://prove2.me/submissions/d1eb828d-9944-4850-8029-4d9a51a79eba

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Derived
open Regularity HQuot Hadamard ClusterMatrix Ledger
namespace FriedCrossing.Derived
theorem _root_.solution : (1 : WithTop ℕ∞) + 1 ≤ 2 := by norm_num
end FriedCrossing.Derived
