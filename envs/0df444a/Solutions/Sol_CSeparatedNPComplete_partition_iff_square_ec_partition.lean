-- Prove2me | solution 1 for CSeparatedNPComplete.partition_iff_square_ec_partition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:59:03.111811+00:00
-- url     : https://prove2.me/submissions/48b98bab-b7d5-48a9-bd0c-1413c426f63b

module
public import Definitions.Def_CSeparatedNPComplete
public import Definitions.Def_CSeparatedNPComplete_Solution
public import Theorems.Thm_CSeparatedNPComplete_SquareReduction_exists_ec_partition_iff


set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete
namespace CSeparatedNPComplete
theorem _root_.solution (n : ℕ) (a : Fin n → ℕ) :
    SquareReduction.HasPartition a ↔
      ∃ x : Vec (n + n), is_ec_partition x (SquareReduction.values a) :=
  (SquareReduction.exists_ec_partition_iff a).symm
end CSeparatedNPComplete
