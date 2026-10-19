-- Prove2me | solution 1 for ContWeatherall.h1Vanishes
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T23:51:06.289703+00:00
-- url     : https://prove2.me/submissions/6aa801b9-fa31-460a-8192-fb99cffc2064

import Theorems.Thm_ContWeatherall_poincare

open CategoryTheory ContinuousAlternatingMap ContWeatherall
open scoped ContDiff

theorem solution (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] : H1Vanishes E F := by
  intro A hA hclosed
  obtain ⟨η, hη, hdη⟩ := poincare (k := 0) hA hclosed
  let e := constOfIsEmptyLIE ℝ E F (Fin 0)
  refine ⟨fun x => e.symm (η x), e.symm.contDiff.comp hη, ?_⟩
  have hz : zeroForm (fun x => e.symm (η x)) = η := by
    funext x
    exact e.apply_symm_apply (η x)
  simpa only [grad, hz] using hdη
