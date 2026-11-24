-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.kappa_le_height_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:50:21.89137+00:00
-- url     : https://prove2.me/submissions/35c971f7-1bc5-4a00-8d57-e17c01b453df

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementF
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_Discharge
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_total_le
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_kapC_le_real

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open MvPolynomial Finset Formalism.GM.M Formalism.GM
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution : ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) (LL : Letters N) (a : ℕ) (κ : ℝ),
    (∀ x, LL.deg x ≤ 2 * a) → 2 * a * N + r ≤ p ^ 2 * (8 * a + r) ^ 2 →
    ((N + 2) * r ^ 2 : ℝ) * lgV2 p a r ≤ κ → kapC p r LL.total ≤ ⌈κ / (N + 2)⌉₊ := by
  intro p _ N r LL a κ hdeg hpa hκ
  have htot := total_le LL (2 * a) hdeg
  have hk := kapC_le_real p r LL.total a (le_trans (Nat.add_le_add_right htot r) hpa)
  have hpos : (0 : ℝ) < (N : ℝ) + 2 := by positivity
  have hb : (r : ℝ) ^ 2 * lgV2 p a r ≤ κ / ((N : ℝ) + 2) := by
    rw [le_div_iff₀ hpos]
    calc (r : ℝ) ^ 2 * lgV2 p a r * ((N : ℝ) + 2) = ((N + 2) * r ^ 2 : ℝ) * lgV2 p a r := by ring
      _ ≤ κ := hκ
  exact Nat.cast_le.1 ((hk.trans hb).trans (Nat.le_ceil _))
end Formalism.InvariantFactorPaths.PW
