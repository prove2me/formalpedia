-- Prove2me | solution 1 for Formalism.DivisionValues.young_diagram_origin_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:18.848821+00:00
-- url     : https://prove2.me/submissions/1bf5adac-d681-49a4-94c7-2d2f85d3a05e

import Definitions.Def_Formalism_QuotientMetricDivisors_TheoremDivIneqRowsShift
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_YoungDiagramHook
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_YoungDiagramTopExact
import Theorems.Thm_Formalism_DivisionValues_RowsOrigin_top_core
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
theorem _root_.solution : RowsOriginTop := by
  intro n j t w s wr aT bT m Sc Bl sh u v νr ar blk sm hj hs hw hν ha hint hu0 hul hlo hhi hsh hB
  obtain ⟨eν, ea⟩ := RowsOrigin.origin_rewrite hj hs hw hν ha
  obtain ⟨H1, H2⟩ := RowsOrigin.origin_interlace eν ea hint
  have hT : (((j - 1) * t : ℕ) : ℝ) = ((j : ℝ) - 1) * (t : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_sub hj]; simp
  refine RowsOrigin.top_core νr ar blk sm H1 H2 ?_ ?_ ?_ ?_ (by rw [hT]; exact hsh) hB
  · have h3 := eν 0
    simp only [Fin.val_zero, Nat.cast_zero] at h3
    rw [hu0] at h3
    have : (νr 0 : ℝ) = (aT : ℝ) + (wr : ℝ) := by linarith
    exact_mod_cast this
  · have h3 := eν (Fin.last (n + 1))
    rw [Fin.val_last, hul] at h3
    push_cast at h3
    have hb : (0 : ℝ) ≤ (bT : ℝ) := Nat.cast_nonneg _
    have : (νr (Fin.last (n + 1)) : ℝ) ≤ (wr : ℝ) := by linarith
    exact_mod_cast this
  · have h3 := ea (Fin.last n)
    rw [Fin.val_last] at h3
    have : (wr : ℝ) + (((j - 1) * t : ℕ) : ℝ) ≤ (ar (Fin.last n) : ℝ) := by linarith
    exact_mod_cast this
  · have h3 := ea 0
    simp only [Fin.val_zero, Nat.cast_zero] at h3
    linarith
end Formalism.DivisionValues
