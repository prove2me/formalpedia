-- Prove2me | solution 1 for Formalism.FT.SymmetricSeries.toFinsupp_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:43:47.663556+00:00
-- url     : https://prove2.me/submissions/f1c3821f-7de5-4ed0-a500-a111ed31ae40

import Definitions.Def_Formalism_ArtinHasse_Statement
import Definitions.Def_Formalism_ArtinHasse_ArtinHasseProofs_SymmSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.FT Formalism.FT.SymmetricSeries
variable {σ R : Type*} [CommRing R] [Fintype σ] [DecidableEq σ]
namespace Formalism.FT.SymmetricSeries
theorem _root_.solution (s : Multiset σ) : ∑ i, Multiset.toFinsupp s i = Multiset.card s := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [← Multiset.singleton_add, Multiset.toFinsupp_add, Multiset.toFinsupp_singleton]
    simp only [Finsupp.add_apply, Finset.sum_add_distrib, ih, Finsupp.single_apply]
    simp [add_comm]
end Formalism.FT.SymmetricSeries
