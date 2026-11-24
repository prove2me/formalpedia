-- Prove2me | solution 1 for Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.DetPolyCore.base
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:00.715648+00:00
-- url     : https://prove2.me/submissions/71e91fec-1ea0-40f2-803c-93d0c29a09fd

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
open Formalism Formalism.TruncatedSeriesCounting Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.DetPolyCore
variable {R : Type*} [CommRing R] {G : Type*} [Monoid G] {n : Type} [Fintype n] [DecidableEq n]
variable (N : ℕ)
variable {S : Subring R}
namespace Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.DetPolyCore
theorem _root_.solution (ρ : G →* Matrix n n R) (l : List (R × ℕ × G)) (hl : ∀ L ∈ l, N + 1 ≤ L.2.1) :
    piN N (F ρ l) = 1 := by
  unfold F
  rw [RingHom.map_det, map_sub, map_one, map_list_sum, List.map_map]
  have h0 : (l.map ((piN N).mapMatrix ∘ term ρ)).sum = 0 := by
    apply List.sum_eq_zero
    intro M hM
    obtain ⟨L, hL, rfl⟩ := List.mem_map.mp hM
    exact mapMatrix_smul_zero N (piN_eq_zero N (hl L hL)) _
  rw [h0, sub_zero, Matrix.det_one]
end Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.DetPolyCore
