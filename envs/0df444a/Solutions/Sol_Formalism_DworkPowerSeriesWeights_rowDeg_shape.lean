-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.rowDeg_shape
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:53.744799+00:00
-- url     : https://prove2.me/submissions/38b56b01-de81-4cd1-9069-c59cc34b7301

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementI
import Definitions.Def_Formalism_GaussJetBounds_MonoShapeTop
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs


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
theorem _root_.solution {d N0 N1 p : ℕ} (s s' : ZMod d) (k : Fin N0) (τ : Fin p → Fin N0)
    (I : Fin p → Fin N1) :
    rowDeg s' k (∑ i, Finsupp.single ((s, τ i, I i) : ZV d N0 N1) 1) =
      if s' = s then (Finset.univ.filter (fun i => τ i = k)).card else 0 := by
  classical
  simp only [rowDeg, Finsupp.finsetSum_apply, Finsupp.single_apply, Prod.mk.injEq]
  rw [Finset.sum_comm]
  by_cases hs : s' = s
  · subst hs
    rw [if_pos rfl, Finset.card_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : τ i = k
    · simp [h]
    · simp [h]
  · rw [if_neg hs]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun b _ => ?_
    rw [if_neg]
    intro hh
    exact hs hh.1.symm
end Formalism.DworkPowerSeriesWeights
