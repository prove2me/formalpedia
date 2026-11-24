-- Prove2me | solution 1 for Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.DetPolyCore.letter_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:51:15.562178+00:00
-- url     : https://prove2.me/submissions/f7b50d6b-c8c5-491f-ac79-279f77a63730

import Definitions.Def_Formalism_TruncatedSeriesCounting_LemmaDetPoly
import Definitions.Def_Formalism_TruncatedSeriesCounting_TruncatedSeriesProofs_LemmaDetPoly
import Theorems.Thm_Formalism_TruncatedSeriesCounting_TruncatedSeriesCountingIdentities_DetPolyCore_C_mem_polyS
import Theorems.Thm_Formalism_TruncatedSeriesCounting_TruncatedSeriesCountingIdentities_DetPolyCore_X_mem_polyS
import Theorems.Thm_Formalism_TruncatedSeriesCounting_TruncatedSeriesCountingIdentities_DetPolyCore_comp_mem_polyS
import Theorems.Thm_Formalism_TruncatedSeriesCounting_TruncatedSeriesCountingIdentities_DetPolyCore_charpoly_comp

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
theorem _root_.solution (ρ : G →* Matrix n n R) (hS : ∀ g k, (Matrix.charpolyRev (ρ g)).coeff k ∈ S)
    (L : R × ℕ × G) (hc : L.1 ∈ S) : piN N (Matrix.det (1 - term ρ L)) ∈ SQ N S := by
  rw [charpoly_comp]
  exact ⟨_, comp_mem_polyS (fun k => hS _ k)
    ((polyS S).mul_mem (C_mem_polyS hc) ((polyS S).pow_mem X_mem_polyS _)), rfl⟩
end Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.DetPolyCore
