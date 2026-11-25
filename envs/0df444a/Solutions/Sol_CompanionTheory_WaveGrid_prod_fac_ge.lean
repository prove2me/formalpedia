-- Prove2me | solution 1 for CompanionTheory.WaveGrid.prod_fac_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:07:14.187668+00:00
-- url     : https://prove2.me/submissions/5d76b9ce-a339-4927-afea-f0d446072694

import Definitions.Def_Formalism_HermitianCurvature_StatementD
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_QwBound
import Theorems.Thm_CompanionTheory_WaveGrid_fac_ge

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory CompanionTheory.WaveGrid
open Formalism.FourierDecayAlt
namespace CompanionTheory.WaveGrid
theorem _root_.solution (w : List C.Letter) (y : ℝ) (h : ∀ l ∈ w, 4 ≤ |y - l.2|) :
    (3 / 4 : ℝ) ^ w.length ≤ (w.map fun l => fac l y).prod := by
  induction w with
  | nil => simp
  | cons l w ih =>
    simp only [List.length_cons, List.map_cons, List.prod_cons, pow_succ]
    have h1 := fac_ge l y (h l (by simp))
    have h2 := ih fun l' hl' => h l' (by simp [hl'])
    rw [mul_comm]
    exact mul_le_mul h1 h2 (by positivity) (by linarith)
end CompanionTheory.WaveGrid
