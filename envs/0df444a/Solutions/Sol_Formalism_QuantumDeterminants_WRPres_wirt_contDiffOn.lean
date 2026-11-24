-- Prove2me | solution 1 for Formalism.QuantumDeterminants.WRPres.wirt_contDiffOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:12:42.780637+00:00
-- url     : https://prove2.me/submissions/3cd9b535-66ef-42f7-8ded-9ee8da13c38a

import Definitions.Def_Formalism_FormalDegreeBessel_StatementWR
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_WRPres
import Theorems.Thm_Formalism_QuantumDeterminants_WRPres_fderiv_apply_contDiffOn

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
theorem _root_.solution {f : (Fin m → ℂ) → E} (hf : ContDiffOn ℝ ∞ f (OmX m)) (l : Fin m) :
    ContDiffOn ℝ ∞ (wirt l f) (OmX m) := by
  unfold wirt
  exact ((fderiv_apply_contDiffOn hf _).sub ((fderiv_apply_contDiffOn hf _).const_smul _)).const_smul _
end Formalism.QuantumDeterminants.WRPres
