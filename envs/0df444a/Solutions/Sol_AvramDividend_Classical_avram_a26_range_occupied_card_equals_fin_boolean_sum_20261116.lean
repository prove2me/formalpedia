-- Prove2me | solution 1 for AvramDividend.Classical.avram_a26_range_occupied_card_equals_fin_boolean_sum_20261116
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T08:19:46.566257+00:00
-- url     : https://prove2.me/submissions/cc569b05-0e17-4d75-8e5e-03e2431ba035

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open scoped BigOperators
noncomputable section
theorem solution
    (n : ℕ) (b : ℕ → Prop) [DecidablePred b] :
    ((Finset.range n).filter b).card =
      ∑ i : Fin n, if b i.val then (1 : ℕ) else 0 := by
  classical
  rw [Finset.card_filter]
  exact (Fin.sum_univ_eq_sum_range
    (fun i : ℕ => if b i then (1 : ℕ) else 0) n).symm
