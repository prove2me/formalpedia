-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HLsc.sum_sub_le_tsum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:12:53.902691+00:00
-- url     : https://prove2.me/submissions/a6f4492f-41c1-4081-87df-3afd3d39fcbe

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Herglotz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HerglotzLowerSemicontinuous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HLsc
open Real Filter Topology Finset MeasureTheory Formalism.FourierDecayAlt.P.Herglotz
variable {d : ℕ}
namespace Formalism.FourierDecayAlt.P.HLsc
theorem _root_.solution {κ : (Fin d → ℤ) → ℝ} (hκ0 : ∀ σ, 0 ≤ κ σ) (hκ : Summable κ)
    (B : Finset (Fin d → ℤ)) (σ : Fin d → ℤ) :
    ∑ σ' ∈ B, κ (σ - σ') ≤ ∑' τ, κ τ := by
  rw [← (Equiv.subLeft σ).tsum_eq κ]
  exact ((Equiv.subLeft σ).summable_iff.2 hκ).sum_le_tsum B (fun i _ => hκ0 _)
end Formalism.FourierDecayAlt.P.HLsc
