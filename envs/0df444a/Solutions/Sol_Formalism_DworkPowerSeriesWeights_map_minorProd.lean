-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.map_minorProd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:04:39.816536+00:00
-- url     : https://prove2.me/submissions/608853db-4a2f-4926-96b8-516f3e7650a5

import Definitions.Def_Formalism_GaussJetBounds_StatementJ
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP

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
theorem _root_.solution {R : Type u} [CommRing R] {σ σ' : Type} {N0 N1 C : ℕ}
    (φ : MvPolynomial σ R →ₐ[R] MvPolynomial σ' R)
    (row : Fin N0 → Fin N1 → MvPolynomial σ R) (p : Fin C → ℕ) (hp : ∀ c, p c ≤ N0)
    (I : ∀ c, Fin (p c) → Fin N1) :
    φ (minorProd row p hp I) = minorProd (fun i b => φ (row i b)) p hp I := by
  unfold minorProd
  rw [map_prod]
  refine Finset.prod_congr rfl (fun c _ => ?_)
  rw [AlgHom.map_det]
  congr 1
end Formalism.DworkPowerSeriesWeights
