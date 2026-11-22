-- Prove2me | solution 1 for Formalism.QuantumDeterminants.gn_herm_bvec_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:09:17.937516+00:00
-- url     : https://prove2.me/submissions/46664508-95e9-422b-b56f-ce2074453f93

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GNonneg

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
theorem _root_.solution {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (v : Fin m → ℂ) (j : Fin m) :
    herm H v (bvec j) = (H *ᵥ v) j := by
  simp only [herm, bvec, _root_.dotProduct, Pi.star_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · intro h
    exact absurd (Finset.mem_univ _) h
end Formalism.QuantumDeterminants
