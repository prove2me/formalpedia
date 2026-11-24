-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.divAB_of_suppOK
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:36:24.56979+00:00
-- url     : https://prove2.me/submissions/14f8bd1b-2d0a-49f1-ae34-02c7d89c0fb5

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NormLiftLeOne

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
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution {K : Type} [Field K] {p : ℕ} {G : MvPowerSeries (Fin 2) K}
    (h : SuppOK p G) : DivAB G := by
  intro n hn
  by_contra hc
  obtain ⟨h0, h1, -⟩ := h n hc
  omega
end Formalism.InvariantFactorPaths.G7
