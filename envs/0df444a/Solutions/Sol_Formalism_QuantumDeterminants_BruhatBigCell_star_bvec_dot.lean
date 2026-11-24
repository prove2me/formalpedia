-- Prove2me | solution 1 for Formalism.QuantumDeterminants.BruhatBigCell.star_bvec_dot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:12:34.889485+00:00
-- url     : https://prove2.me/submissions/46c0342b-0f9e-41aa-a737-e78c8c8c5b0f

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
theorem _root_.solution {m : ℕ} (e : Fin m) (w : Fin m → ℂ) : star (bvec e) ⬝ᵥ w = w e := by
  rw [dotProduct, Finset.sum_eq_single e]
  · simp [bvec]
  · intro p _ hp; simp [bvec, hp]
  · intro h; exact absurd (Finset.mem_univ _) h
end Formalism.QuantumDeterminants.BruhatBigCell
