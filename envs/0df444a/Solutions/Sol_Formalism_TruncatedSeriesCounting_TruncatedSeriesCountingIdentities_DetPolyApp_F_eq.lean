-- Prove2me | solution 1 for Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.DetPolyApp.F_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:37:23.893812+00:00
-- url     : https://prove2.me/submissions/fbed2876-fd43-4196-803f-8c7110e6ea78

import Definitions.Def_Formalism_TruncatedSeriesCounting_LemmaDetPoly
import Definitions.Def_Formalism_TruncatedSeriesCounting_TruncatedSeriesProofs_LemmaDetPoly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical Polynomial
noncomputable section
open Formalism Formalism.TruncatedSeriesCounting Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.DetPolyApp
open DetPolyCore
variable {K Xs G : Type*} [CommRing K] [Monoid G] {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.DetPolyApp
theorem _root_.solution {R : Type*} [CommRing R] (ρ : G →* Matrix n n R) (l : List (R × ℕ × G))
    (hl : ∀ L ∈ l, L.2.1 = 1) :
    (l.map (term ρ)).sum = (Polynomial.X : Polynomial R) • ((l.map (fun L => L.1 • ρ L.2.2)).sum).map Polynomial.C := by
  induction l with
  | nil => simp
  | cons L l ih =>
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons,
      ih (fun L' h => hl L' (List.mem_cons_of_mem _ h))]
    have h1 := hl L List.mem_cons_self
    refine Matrix.ext fun i j => ?_
    simp [term, h1]
    ring
end Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.DetPolyApp
