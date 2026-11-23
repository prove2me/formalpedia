-- Prove2me | solution 1 for Formalism.QuantumDeterminants.BruhatBigCell.mulVec_bvec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:10:11.973972+00:00
-- url     : https://prove2.me/submissions/96de471b-f250-4f15-a04b-f11187773cf4

import Definitions.Def_Formalism_FormalDegreeBessel_StatementBF
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GroupFactorizationHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BFCell

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
open Formalism.QuantumDeterminants.BruhatBigCell
open GBasic
namespace Formalism.QuantumDeterminants.BruhatBigCell
theorem _root_.solution {k r : ℕ} (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (e i : Fin (2 * r + k + 1)) : (M *ᵥ bvec e) i = M i e := by
  simp [mulVec, dotProduct, bvec, Pi.single_apply]
end Formalism.QuantumDeterminants.BruhatBigCell
