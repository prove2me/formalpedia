-- Prove2me | solution 1 for Formalism.DivisionValues.RowsOrigin.origin_rewrite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:03:21.173507+00:00
-- url     : https://prove2.me/submissions/fe0691df-8213-48fd-859e-71de4bbe501d

import Definitions.Def_Formalism_QuotientMetricDivisors_TheoremDivIneqRowsShift
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_YoungDiagramHook
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_YoungDiagramTopExact

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
open Formalism.DivisionValues.RowsOrigin
namespace Formalism.DivisionValues.RowsOrigin
theorem _root_.solution {n j t w s wr : ℕ} {m : ℝ} {u : Fin (n + 2) → ℝ} {v : Fin (n + 1) → ℝ}
    {νr : Fin (n + 2) → ℕ} {ar : Fin (n + 1) → ℕ}
    (hj : 1 ≤ j) (hs : (s : ℝ) = (((n : ℝ) + 2) + (2 * (j : ℝ) - 1) * ((t : ℝ) + 1)) / 2)
    (hw : wr + s = w)
    (hν : ∀ i, (νr i : ℝ) = originRow ((n : ℝ) + 2) t j w (u i) ((i : ℕ) + 1))
    (ha : ∀ i, (ar i : ℝ) = originBig ((n : ℝ) + 2) m t j w (v i) ((i : ℕ) + 1)) :
    (∀ i, (νr i : ℝ) = (wr : ℝ) + (u i - (((n : ℝ) + 2) + 1 - 2 * (((i : ℕ) : ℝ) + 1)) / 2)) ∧
    (∀ i, (ar i : ℝ) = (wr : ℝ) + (v i - (((n : ℝ) + 2) - 2 * (((i : ℕ) : ℝ) + 1)) / 2) +
      (((j - 1) * t : ℕ) : ℝ)) := by
  have hw' : (w : ℝ) = (wr : ℝ) + (s : ℝ) := by exact_mod_cast hw.symm
  have hT : (((j - 1) * t : ℕ) : ℝ) = ((j : ℝ) - 1) * (t : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_sub hj]; simp
  constructor
  · intro i
    rw [hν i, originRow, hw', hs]; ring
  · intro i
    rw [ha i, originBig, hw', hs, hT]; ring
end Formalism.DivisionValues.RowsOrigin
