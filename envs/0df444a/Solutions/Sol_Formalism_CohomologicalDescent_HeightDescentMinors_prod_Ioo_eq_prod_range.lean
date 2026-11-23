-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.prod_Ioo_eq_prod_range
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:36:02.798879+00:00
-- url     : https://prove2.me/submissions/1944d16c-bd96-44fc-9054-0e4fcbcfdd18

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution {M : Type} [CommMonoid M] (l : ℕ) (F : ℕ → M) :
    ∏ c ∈ Finset.Ioo 0 l, F c = ∏ k ∈ Finset.range (l - 1), F (k + 1) := by
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · simp
  rw [Finset.range_eq_Ico, Finset.prod_Ico_add' F 0 (l - 1) 1, zero_add, Nat.sub_add_cancel hl]
  rfl
end Formalism.CohomologicalDescent.HeightDescentMinors
