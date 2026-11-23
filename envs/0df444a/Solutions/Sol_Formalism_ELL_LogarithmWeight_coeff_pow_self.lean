-- Prove2me | solution 1 for Formalism.ELL.LogarithmWeight.coeff_pow_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:21:53.476316+00:00
-- url     : https://prove2.me/submissions/d154a075-606a-41a8-af70-2ef3076a4b52

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_UnitCancel
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_LogWeight
import Theorems.Thm_Formalism_ELL_LogarithmWeight_coeff_pow_of_cc

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
theorem _root_.solution {e : PowerSeries K} (he : constantCoeff e = 0) (n : ℕ) :
    coeff n (e ^ n) = coeff 1 e ^ n := by
  obtain ⟨g, hg1, hg⟩ := coeff_pow_of_cc he
  rw [hg, if_pos le_rfl, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, hg1]
end Formalism.ELL.LogarithmWeight
