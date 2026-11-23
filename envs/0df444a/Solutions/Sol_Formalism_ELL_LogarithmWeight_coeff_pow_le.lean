-- Prove2me | solution 1 for Formalism.ELL.LogarithmWeight.coeff_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:26:32.891691+00:00
-- url     : https://prove2.me/submissions/cd5a9b52-883e-475f-9ba3-3594299aefd6

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_UnitCancel
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_LogWeight
import Theorems.Thm_Formalism_ELL_LogarithmWeight_coeff_mul_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL Formalism.ELL.LogarithmWeight
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
namespace Formalism.ELL.LogarithmWeight
theorem _root_.solution {f : PowerSeries K} {c A : ℝ} (hc : 0 < c) (hA : 0 ≤ A)
    (hf : ∀ n, ‖coeff n f‖ * c ^ n ≤ A) (m n : ℕ) :
    ‖coeff n (f ^ m)‖ * c ^ n ≤ A ^ m := by
  induction m generalizing n with
  | zero =>
    rw [pow_zero, pow_zero]
    rcases n with _ | n
    · simp
    · simp [PowerSeries.coeff_one]
  | succ m ih =>
    rw [pow_succ, pow_succ]
    exact coeff_mul_le hc (pow_nonneg hA _) hA ih hf n
end Formalism.ELL.LogarithmWeight
