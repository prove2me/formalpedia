-- Prove2me | solution 1 for Formalism.QuantumDeterminants.WRPres.fderiv_apply_contDiffOn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:06:37.28582+00:00
-- url     : https://prove2.me/submissions/0b4a76bc-de1c-4761-821f-d9f40b7b3268

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
theorem _root_.solution {f : (Fin m → ℂ) → E} (hf : ContDiffOn ℝ ∞ f (OmX m))
    (v : Fin m → ℂ) : ContDiffOn ℝ ∞ (fun x => fderiv ℝ f x v) (OmX m) := by
  exact ((contDiffOn_infty_iff_fderiv_of_isOpen (isOpen_omX m)).1 hf).2.clm_apply contDiffOn_const
end Formalism.QuantumDeterminants.WRPres
