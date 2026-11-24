-- Prove2me | solution 1 for Formalism.REAL.arr_finset_sum_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:34:16.213468+00:00
-- url     : https://prove2.me/submissions/efcf1afa-dfc9-4a26-9b6e-6d9ed208dbc5

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactGeneratorRaisesPfil

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
namespace Formalism.REAL
theorem _root_.solution {j : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Arr V n j) (α : Fin j → Fin n × Fin n) :
    (∑ i ∈ s, f i) α = ∑ i ∈ s, f i α := by
  have h := congrFun (map_sum (arrOf V n j) f s) α
  rw [Finset.sum_apply] at h
  exact h
end Formalism.REAL
