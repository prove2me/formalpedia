-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.minorProd_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:01:50.546745+00:00
-- url     : https://prove2.me/submissions/e384f3fe-d656-4420-b508-250dc4bf9968

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_MonoShapeTop
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormDetLeOneOfEntries
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OneRow

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
theorem _root_.solution {R : Type u} [CommRing R] {σ τ : Type} {N0 N1 Cn : ℕ}
    (φ : MvPolynomial σ R →ₐ[R] MvPolynomial τ R)
    (row : Fin N0 → Fin N1 → MvPolynomial σ R) (p : Fin Cn → ℕ) (hp : ∀ c, p c ≤ N0)
    (I : ∀ c, Fin (p c) → Fin N1) :
    φ (minorProd row p hp I) = minorProd (fun i b => φ (row i b)) p hp I := by
  unfold minorProd
  rw [map_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [AlgHom.map_det]
  rfl
end Formalism.DworkPowerSeriesWeights
