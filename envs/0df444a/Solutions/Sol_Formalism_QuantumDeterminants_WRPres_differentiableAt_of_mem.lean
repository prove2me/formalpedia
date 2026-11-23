-- Prove2me | solution 1 for Formalism.QuantumDeterminants.WRPres.differentiableAt_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:20:00.514012+00:00
-- url     : https://prove2.me/submissions/03687652-040e-474a-9f77-a0a9f90ad15b

import Definitions.Def_Formalism_FormalDegreeBessel_StatementWR
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_WRPres
import Theorems.Thm_Formalism_QuantumDeterminants_WRPres_isOpen_omX

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.QuantumDeterminants.WRPres
variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.QuantumDeterminants.WRPres
theorem _root_.solution {f : (Fin m → ℂ) → E} (hf : f ∈ WSm m E) {x : Fin m → ℂ}
    (hx : x ∈ OmX m) : DifferentiableAt ℝ f x := by
  have h1 : ContDiffOn ℝ ∞ f (OmX m) := hf.1
  exact (h1.differentiableOn (by simp)).differentiableAt ((isOpen_omX m).mem_nhds hx)
end Formalism.QuantumDeterminants.WRPres
