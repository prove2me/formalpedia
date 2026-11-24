-- Prove2me | solution 1 for Formalism.GM.alternatingChooseSum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:34:09.281371+00:00
-- url     : https://prove2.me/submissions/1c219ebf-e0f1-4aa2-a2d7-97adaea730ca

import Definitions.Def_Formalism_MahlerMeasure_LevelSum
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelSum
import Theorems.Thm_Formalism_GM_altVand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open Finset
namespace Formalism.GM
theorem _root_.solution : LevelSum := by
  intro A z l hzl
  unfold qch
  have hAl : (A.choose l : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  rw [← altVand (A - z - l) z l, Finset.sum_div]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjl : j ≤ l := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hAj : (A.choose j : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have hcm : (A.choose l : ℚ) * (l.choose j : ℚ) = (A.choose j : ℚ) * ((A - j).choose (l - j) : ℚ) := by
    exact_mod_cast Nat.choose_mul (n := A) (k := l) (s := j) (by omega)
  have he : z + (A - z - l) + (l - j) = A - j := by omega
  rw [he, div_eq_div_iff hAj hAl]
  linear_combination ((-1 : ℚ) ^ j * ((A - z - l).choose j : ℚ)) * hcm
end Formalism.GM
