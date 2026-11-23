-- Prove2me | solution 1 for Formalism.ELL.LogarithmWeight.norm_sum_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:09:51.456534+00:00
-- url     : https://prove2.me/submissions/5cfb9deb-20f9-4dae-9c6d-b3f972fd728f

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
theorem _root_.solution {ι : Type*} (s : Finset ι) (f : ι → K) {w B : ℝ} (hw : 0 < w)
    (hB : 0 ≤ B) (h : ∀ i ∈ s, ‖f i‖ * w ≤ B) : ‖∑ i ∈ s, f i‖ * w ≤ B := by
  rw [← le_div_iff₀ hw]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (div_nonneg hB hw.le)
  intro i hi
  rw [le_div_iff₀ hw]
  exact h i hi
end Formalism.ELL.LogarithmWeight
