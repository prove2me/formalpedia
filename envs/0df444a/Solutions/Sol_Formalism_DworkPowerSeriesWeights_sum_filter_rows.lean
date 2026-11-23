-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.sum_filter_rows
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:06:07.646525+00:00
-- url     : https://prove2.me/submissions/fe90e23a-d533-4fb2-bcad-527026c46215

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
theorem _root_.solution {d N0 N1 : ℕ} [NeZero d] (Pr : ZMod d × Fin N0 → Prop) [DecidablePred Pr]
    (κ : ZV d N0 N1 →₀ ℕ) :
    (∑ y ∈ Finset.univ.filter (fun y : ZV d N0 N1 => Pr (y.1, y.2.1)), κ y) =
      ∑ r ∈ Finset.univ.filter Pr, rowDeg r.1 r.2 κ := by
  classical
  rw [Finset.sum_filter, Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases h : Pr (s, k)
  · simp [h, rowDeg]
  · simp [h]
end Formalism.DworkPowerSeriesWeights
