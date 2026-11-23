-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.rowOp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:04:45.646259+00:00
-- url     : https://prove2.me/submissions/db1f94c4-cbfe-426e-8aa8-65e81601b887

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
theorem _root_.solution {K : Type u} [Field K] {d N0 N1 : ℕ} (TT : Finset (ZMod d))
    (T : ZMod d → Fin N0 → Fin N0 → K) (s : ZMod d) (i : Fin N0) (b : Fin N1) :
    rowOp (N1 := N1) TT T s i b = ∑ k, C (opA TT T s i k) * X (s, k, b) := by
  unfold rowOp opA
  split_ifs with h
  · rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hk
      simp [hk]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  · refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> simp
end Formalism.DworkPowerSeriesWeights
