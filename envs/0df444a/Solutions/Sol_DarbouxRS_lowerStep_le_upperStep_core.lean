-- Prove2me | solution 1 for DarbouxRS.lowerStep_le_upperStep_core
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T23:44:02.223835+00:00
-- url     : https://prove2.me/submissions/cf76f17e-dc62-41e6-9c02-34180a3b8d06

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F000
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open DarbouxRS
open scoped BigOperators Pointwise
noncomputable section

theorem solution {a b : ℝ} (P : Partition a b)
    {f : ℝ → ℝ} (i : Fin P.n)
    (hBelow : BddBelow (f '' Set.Icc a b))
    (hAbove : BddAbove (f '' Set.Icc a b)) :
    lowerStep P f i ≤ upperStep P f i := by
  have hcell_nonempty : (f '' Partition.subinterval P i).Nonempty := by
    -- We show the image is non-empty by plugging in the left endpoint
    refine ⟨f (P.pts i.castSucc), ?_⟩
    exact ⟨P.pts i.castSucc, ⟨le_rfl, le_of_lt (P.strict_mono (Fin.castSucc_lt_succ))⟩, rfl⟩

  have hcellBelow : BddBelow (f '' Partition.subinterval P i) :=
    BddBelow.mono (Set.image_mono (subinterval_subset_Icc_core P)) hBelow

  have hcellAbove : BddAbove (f '' Partition.subinterval P i) :=
    BddAbove.mono (Set.image_mono (subinterval_subset_Icc_core P)) hAbove

  rcases hcell_nonempty with ⟨y, hy⟩
  unfold lowerStep upperStep

  -- inf(f) ≤ y and y ≤ sup(f), therefore inf(f) ≤ sup(f)
  exact le_trans (csInf_le hcellBelow hy) (le_csSup hcellAbove hy)
