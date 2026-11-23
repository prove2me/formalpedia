-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.generic_norm_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:01:27.999593+00:00
-- url     : https://prove2.me/submissions/041881c4-9b30-4f58-bf20-a93f1b90229f

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementM
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FrameA
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Special
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Generic

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
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {K : Type u} [NormedField K] {σ : Type} {l : ℕ} (hl : l.Prime)
    (Y : σ → K) (hY : IsGeneric l Y) (y : σ) : ‖Y y‖ = 1 := by
  haveI : Fact (1 < l) := ⟨hl.one_lt⟩
  have h := hY (MvPolynomial.X y) (by
    rw [MvPolynomial.map_X]
    exact MvPolynomial.X_ne_zero y)
  simpa using h
end Formalism.DworkPowerSeriesWeights
