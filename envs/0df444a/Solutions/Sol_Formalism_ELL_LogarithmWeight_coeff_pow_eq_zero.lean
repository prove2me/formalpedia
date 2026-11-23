-- Prove2me | solution 1 for Formalism.ELL.LogarithmWeight.coeff_pow_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:18:57.962983+00:00
-- url     : https://prove2.me/submissions/80c3cfa8-8dc1-4c77-a59e-68834c745f04

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
theorem _root_.solution {e : PowerSeries K} (he : constantCoeff e = 0) {m n : ℕ} (h : n < m) :
    coeff n (e ^ m) = 0 := by
  obtain ⟨g, -, hg⟩ := coeff_pow_of_cc he
  rw [hg, if_neg (by omega)]
end Formalism.ELL.LogarithmWeight
