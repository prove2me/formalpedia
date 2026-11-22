-- Prove2me | solution 1 for Formalism.QuantumDeterminants.mF_col
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:09:26.003359+00:00
-- url     : https://prove2.me/submissions/53501c87-7aad-45ee-af1a-aace024a28cf

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GroupFactorizationHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.QuantumDeterminants
namespace Formalism.QuantumDeterminants
theorem _root_.solution {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ)
    (m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i : Fin (2 * r + k + 1))
    (a : Fin (r + 1)) (hA : a.val < r) :
    (m * Fm k r z) i a = m i (eI k r ⟨a.val, hA⟩) := by
  change (m *ᵥ fvec k r z a) i = _
  simp [fvec, hA, bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
end Formalism.QuantumDeterminants
