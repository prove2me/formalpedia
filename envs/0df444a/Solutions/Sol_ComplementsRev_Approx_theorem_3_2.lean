-- Prove2me | solution 1 for ComplementsRev.Approx.theorem_3_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T15:08:01.803456+00:00
-- url     : https://prove2.me/submissions/d930abfb-d39e-4a34-86c0-52a7016c43bb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ComplementsRev_Approx_Setting
import Theorems.Thm_ComplementsRev_Approx_corollary_3_1
import Theorems.Thm_ComplementsRev_Approx_proposition_4_1
import Theorems.Thm_ComplementsRev_Approx_proposition_5_10

open ComplementsRev.Approx

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Population ι) (d : ℕ) (hd : HasComplementarity P d)
    (m : Mech ι) (hm : IsTruthful P m) :
    revenue P m ≤ (4 * (d : ℝ) + 16) * max (BREV P) (SREVstar P) := by
  let rk : Finset ι → ℕ := fun S => (Fintype.equivFin (Finset ι) S).val
  have hrk : Function.Injective rk := by
    intro a b h
    exact (Fintype.equivFin (Finset ι)).injective (Fin.ext h)
  have h1 := corollary_3_1 P rk hrk m hm
  have h2 := proposition_4_1 P d hd rk hrk
  have h3 := proposition_5_10 P rk hrk
  have hB : BREV P ≤ max (BREV P) (SREVstar P) := le_max_left _ _
  have hS : SREVstar P ≤ max (BREV P) (SREVstar P) := le_max_right _ _
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  nlinarith [mul_le_mul_of_nonneg_left hS hd0]
