-- Prove2me | solution 1 for CSeparatedNPComplete.SquareReduction.paired_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:54:50.680794+00:00
-- url     : https://prove2.me/submissions/49b6f19a-15cb-4d85-ba71-d9b70f70ca38

module
public import Definitions.Def_CSeparatedNPComplete_SquarePartition
public import Definitions.Def_CSeparatedNPComplete_SquareReduction

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.SquareReduction
namespace CSeparatedNPComplete.SquareReduction
theorem _root_.solution {n : ℕ} (p : Vec n) :
    dot (Fin.append p (1 - p)) 1 = ((n + n : ℕ) : ℝ) / 2 := by
  simp only [dot, Fin.sum_univ_add, Fin.append_left, Fin.append_right,
    Pi.one_apply, Pi.sub_apply, mul_one]
  rw [← Finset.sum_add_distrib]
  simp
end CSeparatedNPComplete.SquareReduction
