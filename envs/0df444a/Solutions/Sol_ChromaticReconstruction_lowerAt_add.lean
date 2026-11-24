-- Prove2me | solution 1 for ChromaticReconstruction.lowerAt_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:26:26.34625+00:00
-- url     : https://prove2.me/submissions/d65e0597-3480-4d27-bfb7-b4c0d9593f3d

import Definitions.Def_RequestProject_CompStructure
import Definitions.Def_RequestProject_RecoverP

set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution {W : Multiset ℕ} {a : ℕ} (ha : a ∈ W) :
    lowerAt W a + {a} = W + {a - 1} := by
  unfold lowerAt
  conv_rhs => rw [← Multiset.cons_erase ha]
  rw [Multiset.cons_add, Multiset.cons_add, Multiset.add_comm _ ({a} : Multiset ℕ),
    Multiset.add_comm _ ({a - 1} : Multiset ℕ), Multiset.singleton_add, Multiset.singleton_add]
  exact Multiset.cons_swap _ _ _
end ChromaticReconstruction
