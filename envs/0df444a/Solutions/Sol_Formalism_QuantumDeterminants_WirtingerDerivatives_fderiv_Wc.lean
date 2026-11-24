-- Prove2me | solution 1 for Formalism.QuantumDeterminants.WirtingerDerivatives.fderiv_Wc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:43:10.773602+00:00
-- url     : https://prove2.me/submissions/ab0478a0-ac3d-4c79-8828-c2278fbbdf62

import Definitions.Def_Formalism_FormalDegreeBessel_StatementWR
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_WRWeyl
import Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_diff_fderiv

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
    (u w : Fin m → ℂ) (s : ℂ) :
    fderiv ℝ (fun y => Wc u w s (fderiv ℝ g y)) x = (Wc u w s).comp (fderiv ℝ (fderiv ℝ g) x) := by
  exact ((Wc u w s).hasFDerivAt.comp x (diff_fderiv hg).hasFDerivAt).fderiv
end Formalism.QuantumDeterminants.WirtingerDerivatives
