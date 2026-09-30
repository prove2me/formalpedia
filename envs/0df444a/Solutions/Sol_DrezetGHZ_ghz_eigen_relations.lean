-- Prove2me | solution 1 for DrezetGHZ.ghz_eigen_relations
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:11:06.760342+00:00
-- url     : https://prove2.me/submissions/07bbee8f-fe33-4bb7-aee8-d53338e36917

import Definitions.Def_DrezetGHZ_Quantum

set_option autoImplicit false
open DrezetGHZ Matrix

theorem solution :
    tensor3 pauliX pauliX pauliX *ᵥ ghzState = -ghzState ∧
    tensor3 pauliX pauliY pauliY *ᵥ ghzState = ghzState ∧
    tensor3 pauliY pauliX pauliY *ᵥ ghzState = ghzState ∧
    tensor3 pauliY pauliY pauliX *ᵥ ghzState = ghzState := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    funext ⟨i, j, k⟩ <;>
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num [Matrix.mulVec, dotProduct, tensor3, Matrix.kronecker_apply,
      pauliX, pauliY, ghzState, Fintype.sum_prod_type, Fin.sum_univ_two] <;>
    ring_nf <;> simp [Complex.I_sq]
