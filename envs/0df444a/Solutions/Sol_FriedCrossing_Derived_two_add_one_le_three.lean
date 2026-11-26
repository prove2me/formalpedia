-- Prove2me | solution 1 for FriedCrossing.Derived.two_add_one_le_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:41:00.034771+00:00
-- url     : https://prove2.me/submissions/8bddc051-516d-44f5-bd5b-0866a7bdd6c0

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Derived
open Regularity HQuot Hadamard ClusterMatrix Ledger
namespace FriedCrossing.Derived
theorem _root_.solution : (2 : WithTop ℕ∞) + 1 ≤ 3 := by norm_num
end FriedCrossing.Derived
