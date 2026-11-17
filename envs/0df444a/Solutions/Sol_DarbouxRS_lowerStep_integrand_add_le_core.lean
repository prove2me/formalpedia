-- Prove2me | solution 1 for DarbouxRS.lowerStep_integrand_add_le_core
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T23:44:17.96993+00:00
-- url     : https://prove2.me/submissions/06be4741-7ebd-4aab-b970-3989e6ccb832

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F000
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open DarbouxRS
open scoped BigOperators Pointwise
noncomputable section

theorem solution {a b : ℝ} {f g : ℝ → ℝ}
    (P : Partition a b)
    (i : Fin P.n)
    (hfBelow : BddBelow (f '' Set.Icc a b))
    (hgBelow : BddBelow (g '' Set.Icc a b)) :
    lowerStep P f i + lowerStep P g i ≤ lowerStep P (fun x => f x + g x) i := by
  have hcell_nonempty : ((fun x => f x + g x) '' Partition.subinterval P i).Nonempty := by
    -- Evaluate the function at the left endpoint of the interval
    refine ⟨f (P.pts i.castSucc) + g (P.pts i.castSucc), ?_⟩
    exact ⟨P.pts i.castSucc, ⟨le_rfl, le_of_lt (P.strict_mono (Fin.castSucc_lt_succ))⟩, rfl⟩

  have hfCellBelow : BddBelow (f '' Partition.subinterval P i) :=
    BddBelow.mono (Set.image_mono (subinterval_subset_Icc_core P)) hfBelow

  have hgCellBelow : BddBelow (g '' Partition.subinterval P i) :=
    BddBelow.mono (Set.image_mono (subinterval_subset_Icc_core P)) hgBelow

  unfold lowerStep
  refine le_csInf hcell_nonempty ?_
  rintro y ⟨x, hx, rfl⟩

  have hfx : sInf (f '' Partition.subinterval P i) ≤ f x :=
    csInf_le hfCellBelow ⟨x, hx, rfl⟩

  have hgx : sInf (g '' Partition.subinterval P i) ≤ g x :=
    csInf_le hgCellBelow ⟨x, hx, rfl⟩

  linarith
