-- Prove2me | solution 1 for Formalism.QuantumDeterminants.ggHerm_bvec_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:33:44.498648+00:00
-- url     : https://prove2.me/submissions/ad934300-f1a2-44b8-b8fc-92e888c13cb6

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_ReverseCauchySchwarzHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option linter.unusedSimpArgs false
noncomputable section
open Formalism Formalism.QuantumDeterminants
namespace Formalism.QuantumDeterminants
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) (v : ι → ℂ)
    (i : ι) : herm H v (Pi.single i 1) = (H *ᵥ v) i := by
  rw [herm]
  have hs : star (Pi.single i (1 : ℂ) : ι → ℂ) = Pi.single i 1 := by
    ext j
    by_cases h : j = i <;> simp [h]
  rw [hs]
  first
  | simp [Matrix.single_dotProduct]
  | simp [dotProduct, Pi.single_apply]
end Formalism.QuantumDeterminants
