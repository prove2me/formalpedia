-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux11.sc_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:43:54.833055+00:00
-- url     : https://prove2.me/submissions/3b47cf92-a751-45bd-8bd8-02d0c53612d6

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeakToStrongSmoothnessReal
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux11_sc_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Set
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux11
variable {k ρ mm : ℕ} {E V : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup V]
  [NormedSpace ℂ V] {a : ℝ} {S : Set (B.Mat k ρ)}
namespace Formalism.FourierDecayAlt.P.Ux11
theorem _root_.solution (c : ℝ) (hc : 0 ≤ c) : ‖sc E c‖ ≤ c :=
  ContinuousLinearMap.opNorm_le_bound _ hc (fun y => by
    rw [sc_apply, norm_smul, Complex.norm_real, Real.norm_of_nonneg hc])
end Formalism.FourierDecayAlt.P.Ux11
