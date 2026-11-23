-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.shape_minor_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:15:39.320183+00:00
-- url     : https://prove2.me/submissions/d4b3dd96-836b-4c56-9bf5-326725919bb3

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementH
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_MinorProductSupportTop
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_shape_minor

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
open MvPolynomial
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {R : Type u} [CommRing R] {J : Type} [Fintype J] [DecidableEq J]
    {N1 p : ℕ} (A : Fin p → J → R) (I : Fin p → Fin N1) (mono : J × Fin N1 →₀ ℕ)
    (hm : mono ∈ (Matrix.of fun (r r' : Fin p) =>
      (∑ j, C (A r j) * X (j, I r') : MvPolynomial (J × Fin N1) R)).det.support) :
    mono ∈ shapeSet A I := by
  have h := shape_minor A I
  rw [mem_restrictSupport_iff] at h
  exact h hm
end Formalism.DworkPowerSeriesWeights
