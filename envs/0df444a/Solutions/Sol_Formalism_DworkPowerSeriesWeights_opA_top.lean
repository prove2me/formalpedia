-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.opA_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:45.013808+00:00
-- url     : https://prove2.me/submissions/ba52ce39-1c8c-4bea-8329-229e8bb12a8b

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
theorem _root_.solution {K : Type u} [Field K] {d N0 : ℕ} (TT : Finset (ZMod d))
    (T : ZMod d → Fin N0 → Fin N0 → K) (s : ZMod d) (hs : s ∈ TT) (i k : Fin N0)
    (h : opA TT T s i k ≠ 0) : i.val = 0 ↔ k.val = 0 := by
  unfold opA at h
  by_cases hi : i.val = 0
  · rw [if_pos ⟨hs, hi⟩] at h
    by_cases hk : k = i
    · rw [hk]
    · rw [if_neg hk] at h
      exact absurd rfl h
  · rw [if_neg (fun hh => hi hh.2)] at h
    by_cases hk : k.val = 0
    · rw [if_pos ⟨hs, hk⟩] at h
      exact absurd rfl h
    · exact ⟨fun hh => absurd hh hi, fun hh => absurd hh hk⟩
end Formalism.DworkPowerSeriesWeights
