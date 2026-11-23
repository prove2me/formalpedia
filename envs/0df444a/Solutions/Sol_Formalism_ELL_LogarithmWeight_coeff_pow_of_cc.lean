-- Prove2me | solution 1 for Formalism.ELL.LogarithmWeight.coeff_pow_of_cc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:02:16.744808+00:00
-- url     : https://prove2.me/submissions/91f2738e-ed51-4b78-96a1-2946ece6e8b9

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_UnitCancel
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_LogWeight

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
theorem _root_.solution {e : PowerSeries K} (he : constantCoeff e = 0) :
    ∃ g : PowerSeries K, constantCoeff g = coeff 1 e ∧
      ∀ m n : ℕ, coeff n (e ^ m) = if m ≤ n then coeff (n - m) (g ^ m) else 0 := by
  obtain ⟨g, hg⟩ := (PowerSeries.X_dvd_iff).mpr he
  refine ⟨g, ?_, fun m n => ?_⟩
  · rw [hg, show (1 : ℕ) = 0 + 1 from rfl, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
  · rw [hg, mul_pow, PowerSeries.coeff_X_pow_mul']
end Formalism.ELL.LogarithmWeight
