-- Prove2me | solution 1 for Formalism.DivisionValues.young_diagram_origin_off
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:18.795923+00:00
-- url     : https://prove2.me/submissions/b13caeb3-9e78-4c24-83fe-be58f037c5d8

import Definitions.Def_Formalism_QuotientMetricDivisors_TheoremDivIneqRowsShift
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_YoungDiagramHook
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_YoungDiagramTopExact
import Theorems.Thm_Formalism_DivisionValues_RowsOrigin_off_core
import Theorems.Thm_Formalism_DivisionValues_RowsOrigin_origin_rewrite
import Theorems.Thm_Formalism_DivisionValues_RowsOrigin_origin_interlace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.DivisionValues
namespace Formalism.DivisionValues
theorem _root_.solution : RowsOriginOff := by
  intro n j t w s wr m Sc Bl sh u v νr ar blk sm hj hs hw hν ha hint hlo hhi hsh hB
  obtain ⟨eν, ea⟩ := RowsOrigin.origin_rewrite hj hs hw hν ha
  obtain ⟨H1, H2⟩ := RowsOrigin.origin_interlace eν ea hint
  have hT : (((j - 1) * t : ℕ) : ℝ) = ((j : ℝ) - 1) * (t : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_sub hj]; simp
  refine RowsOrigin.off_core νr ar blk sm H1 H2 ?_ ?_ (by rw [hT]; exact hsh) hB
  · have h3 := eν (Fin.last (n + 1))
    rw [Fin.val_last] at h3
    push_cast at h3
    have : (wr : ℝ) ≤ (νr (Fin.last (n + 1)) : ℝ) := by linarith
    exact_mod_cast this
  · have h3 := eν 0
    simp only [Fin.val_zero, Nat.cast_zero] at h3
    linarith
end Formalism.DivisionValues
