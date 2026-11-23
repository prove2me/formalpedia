-- Prove2me | solution 1 for Formalism.QuantumDeterminants.WirtingerDerivatives.reg_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:08:29.757005+00:00
-- url     : https://prove2.me/submissions/e72d4d40-dd3b-4071-aca0-7cf436ffb997

import Definitions.Def_Formalism_FormalDegreeBessel_StatementWR
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_WRWeyl
import Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_isOpen_omX

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
theorem _root_.solution {f : (Fin m → ℂ) → E} (hf : f ∈ WSm m E) : Reg f := by
  intro x hx
  exact hf.1.contDiffAt ((isOpen_omX m).mem_nhds hx)
end Formalism.QuantumDeterminants.WirtingerDerivatives
