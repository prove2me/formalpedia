-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.minorProd_mem_opInt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:03:48.269861+00:00
-- url     : https://prove2.me/submissions/cf04f0cf-4ea7-4b60-8903-9396137622b6

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementI
import Definitions.Def_Formalism_GaussJetBounds_MonoShapeTop
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds MvPolynomial
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {K : Type u} [NormedField K] [IsUltrametricDist K] {σ : Type}
    {N0 N1 Cn : ℕ} (row : Fin N0 → Fin N1 → MvPolynomial σ K)
    (hrow : ∀ i b, row i b ∈ opInt K σ) (p : Fin Cn → ℕ) (hp : ∀ c, p c ≤ N0)
    (I : ∀ c, Fin (p c) → Fin N1) : minorProd row p hp I ∈ opInt K σ := by
  unfold minorProd
  refine Subring.prod_mem _ fun c _ => ?_
  rw [Matrix.det_apply]
  refine Subring.sum_mem _ fun π _ => ?_
  rw [Units.smul_def]
  refine zsmul_mem ?_ _
  refine Subring.prod_mem _ fun r _ => ?_
  exact hrow _ _
end Formalism.DworkPowerSeriesWeights
