-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.aeval_int_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:56:35.015802+00:00
-- url     : https://prove2.me/submissions/15d64e40-2320-40bb-9570-cca939e6fd80

import Definitions.Def_Formalism_GaussJetBounds_StatementM
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_GField
import Theorems.Thm_P2M_Formalism_DworkPowerSeriesWeights_eval__ringHom_eq_ab9ee6c66867

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators NNReal
open Formalism Formalism.DworkPowerSeriesWeights
open MvPolynomial
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {σ A K : Type} [CommRing A] [CommRing K] [Algebra ℤ K]
    (ι : MvPolynomial σ A →+* K) (P : MvPolynomial σ ℤ) :
    aeval (fun i => ι (X i)) P = ι (MvPolynomial.map (Int.castRingHom A) P) := by
  rw [aeval_def, ← eval₂_ringHom_eq, eval₂_map]
  congr 1
  exact RingHom.ext_int _ _
end Formalism.DworkPowerSeriesWeights
