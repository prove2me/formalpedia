-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.minorProd_expand
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:01:50.607064+00:00
-- url     : https://prove2.me/submissions/325b8090-ff7d-411f-84fd-3e5c2b1b7278

import Definitions.Def_Formalism_GaussJetBounds_StatementS
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_CoefficientBoundMembership
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_det_sum_mul_expand

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
open MvPolynomial Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {R : Type} [CommRing R] {ι : Type} {N0 N1 Cn : ℕ}
    (x : Fin N0 → Fin N0 → R) (Y : Fin N0 → Fin N1 → MvPolynomial ι R) (p : Fin Cn → ℕ)
    (hp : ∀ c, p c ≤ N0) (I : ∀ c, Fin (p c) → Fin N1) :
    minorProd (fun i b => ∑ a, C (x i a) * Y a b) p hp I =
      ∑ A ∈ Fintype.piFinset (fun c => (Finset.univ : Finset (Fin (p c) → Fin N0))),
        (∏ c, ∏ r', Y (A c r') (I c r')) *
          C (∏ c, (Matrix.of fun (r r' : Fin (p c)) =>
            x ⟨r.val, lt_of_lt_of_le r.isLt (hp c)⟩ (A c r')).det) := by
  simp only [minorProd, det_sum_mul_expand]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [Finset.prod_mul_distrib, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [RingHom.map_det]
  congr 1
end Formalism.DworkPowerSeriesWeights
