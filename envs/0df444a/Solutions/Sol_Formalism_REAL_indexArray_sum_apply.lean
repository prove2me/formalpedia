-- Prove2me | solution 1 for Formalism.REAL.indexArray_sum_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:35:06.274898+00:00
-- url     : https://prove2.me/submissions/0f43937f-8355-4d0d-bcf0-f0b56ae9fd5f

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FirstSlotSliceSlotMixedCasimirZero

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
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n j : ℕ}
namespace Formalism.REAL
theorem _root_.solution {ι : Type*} (s : Finset ι) (f : ι → Arr V n j) (α : Fin j → Fin n × Fin n) :
    (∑ i ∈ s, f i) α = ∑ i ∈ s, f i α := by
  exact map_sum (LinearMap.proj (R := ℂ) (φ := fun _ : Fin j → Fin n × Fin n => V) α ∘ₗ arrOf V n j) f s
end Formalism.REAL
