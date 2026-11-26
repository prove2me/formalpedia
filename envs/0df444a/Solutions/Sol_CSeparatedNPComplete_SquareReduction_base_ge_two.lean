-- Prove2me | solution 1 for CSeparatedNPComplete.SquareReduction.base_ge_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:47:33.638871+00:00
-- url     : https://prove2.me/submissions/3890abee-46b4-4e71-bd5d-c0d237cadddb

module
public import Definitions.Def_CSeparatedNPComplete_SquarePartition
public import Definitions.Def_CSeparatedNPComplete_SquareReduction

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.SquareReduction
namespace CSeparatedNPComplete.SquareReduction
theorem _root_.solution {n : ℕ} (a : Fin n → ℕ) : 2 ≤ base a := by
  unfold base
  omega
end CSeparatedNPComplete.SquareReduction
