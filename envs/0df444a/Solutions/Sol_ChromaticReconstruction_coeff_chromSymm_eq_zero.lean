-- Prove2me | solution 1 for ChromaticReconstruction.coeff_chromSymm_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:20:33.832284+00:00
-- url     : https://prove2.me/submissions/90b3698a-db7c-461c-a8b8-7817af317a27

import Definitions.Def_RequestProject_CompStructure
import Definitions.Def_RequestProject_Uniform
import Definitions.Def_RequestProject_ChromCoeff
import Theorems.Thm_ChromaticReconstruction_coeff_chromSymm
import Theorems.Thm_ChromaticReconstruction_sum_compType


set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V]
namespace ChromaticReconstruction
theorem _root_.solution (G : SimpleGraph V) (μ : Multiset ℕ) (h : μ.sum ≠ Fintype.card V) :
    coeff (Multiset.toFinsupp μ) (chromSymm G) = 0 := by
  rw [coeff_chromSymm]
  apply sum_eq_zero
  intro A hA
  exfalso
  rw [mem_filter] at hA
  exact h (hA.2 ▸ sum_compType _)
end ChromaticReconstruction
