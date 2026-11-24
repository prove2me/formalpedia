-- Prove2me | solution 1 for Formalism.QuantumDeterminants.WirtingerDerivatives.Wc_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:56:35.926942+00:00
-- url     : https://prove2.me/submissions/a171e52c-afb9-476a-9026-92a730b6f35d

import Definitions.Def_Formalism_FormalDegreeBessel_StatementWR
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_WRWeyl
import Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_two_le_smooth
import Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_Wc_apply
import Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_fderiv_Wc

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
theorem _root_.solution {g : (Fin m → ℂ) → E} {x : Fin m → ℂ} (hg : ContDiffAt ℝ ∞ g x)
    (u w : Fin m → ℂ) (s : ℂ) (u' w' : Fin m → ℂ) (s' : ℂ) :
    Wc u w s (fderiv ℝ (fun y => Wc u' w' s' (fderiv ℝ g y)) x) =
      Wc u' w' s' (fderiv ℝ (fun y => Wc u w s (fderiv ℝ g y)) x) := by
  have hs := hg.isSymmSndFDerivAt two_le_smooth
  rw [fderiv_Wc hg, fderiv_Wc hg]
  simp only [Wc_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, map_add, map_smul]
  rw [hs u' u, hs u' w, hs w' u, hs w' w]
  module
end Formalism.QuantumDeterminants.WirtingerDerivatives
