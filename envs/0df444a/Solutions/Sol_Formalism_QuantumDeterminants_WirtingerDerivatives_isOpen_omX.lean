-- Prove2me | solution 1 for Formalism.QuantumDeterminants.WirtingerDerivatives.isOpen_omX
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:12:56.031646+00:00
-- url     : https://prove2.me/submissions/498a6440-13a1-403e-83f1-a683d773abdd

import Definitions.Def_Formalism_FormalDegreeBessel_StatementWR
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_WRWeyl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff Topology
open Filter
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.QuantumDeterminants.WirtingerDerivatives
variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.QuantumDeterminants.WirtingerDerivatives
theorem _root_.solution (m : ℕ) : IsOpen (OmX m) := by
  have : OmX m = ⋂ l : Fin m, {x : Fin m → ℂ | x l ≠ 0} := by ext x; simp [OmX]
  rw [this]
  exact isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const
end Formalism.QuantumDeterminants.WirtingerDerivatives
