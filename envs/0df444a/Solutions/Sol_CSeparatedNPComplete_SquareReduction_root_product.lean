-- Prove2me | solution 1 for CSeparatedNPComplete.SquareReduction.root_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:54:28.767046+00:00
-- url     : https://prove2.me/submissions/cfaf31ab-3dac-4aee-8ed3-26681188a109

module
public import Definitions.Def_CSeparatedNPComplete_SquarePartition
public import Definitions.Def_CSeparatedNPComplete_SquareReduction

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.SquareReduction
namespace CSeparatedNPComplete.SquareReduction
theorem _root_.solution {n : ℕ} (a : Fin n → ℕ) (i : Fin n) :
    upper a i * lower a i = a i * base a ^ (2 * n) := by
  unfold upper lower
  rw [mul_left_comm, ← pow_add]
  congr 2
  omega
end CSeparatedNPComplete.SquareReduction
