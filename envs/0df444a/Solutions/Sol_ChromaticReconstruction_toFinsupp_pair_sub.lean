-- Prove2me | solution 1 for ChromaticReconstruction.toFinsupp_pair_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T15:21:42.89369+00:00
-- url     : https://prove2.me/submissions/8423f377-bc9e-4232-9b1f-1d1d9637d27a

import Definitions.Def_RequestProject_ChromCoeff
import Definitions.Def_RequestProject_Theorem2

set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V W : Type*} [Fintype V] [Fintype W]
namespace ChromaticReconstruction
theorem _root_.solution (s : ℕ) :
    Multiset.toFinsupp (2 ::ₘ Multiset.replicate s 1) - Finsupp.single 2 1 =
      Multiset.toFinsupp (Multiset.replicate s 1) := by
  rw [← Multiset.singleton_add, Multiset.toFinsupp_add, Multiset.toFinsupp_singleton,
    add_tsub_cancel_left]
end ChromaticReconstruction
