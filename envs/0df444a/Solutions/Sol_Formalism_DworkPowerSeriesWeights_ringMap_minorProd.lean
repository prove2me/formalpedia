-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.ringMap_minorProd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:32:10.51055+00:00
-- url     : https://prove2.me/submissions/a0b968b1-ff35-4370-98c6-8faf8b0318b2

import Definitions.Def_Formalism_GaussJetBounds_FrameJetEval
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FJEval

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
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {R S : Type} [CommRing R] [CommRing S] {σ : Type} {N0 N1 C : ℕ}
    (ψ : MvPolynomial σ R →+* MvPolynomial σ S)
    (row : Fin N0 → Fin N1 → MvPolynomial σ R) (p : Fin C → ℕ) (hp : ∀ c, p c ≤ N0)
    (I : ∀ c, Fin (p c) → Fin N1) :
    ψ (minorProd row p hp I) = minorProd (fun i b => ψ (row i b)) p hp I := by
  unfold minorProd
  rw [map_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [RingHom.map_det]
  rfl
end Formalism.DworkPowerSeriesWeights
