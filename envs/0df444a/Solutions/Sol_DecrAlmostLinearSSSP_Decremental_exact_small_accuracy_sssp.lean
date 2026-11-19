-- Prove2me | solution 1 for DecrAlmostLinearSSSP.Decremental.exact_small_accuracy_sssp
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T11:17:00.466219+00:00
-- url     : https://prove2.me/submissions/cdb37465-6e7a-464a-a3c1-54b3535b9fb3

import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_8
set_option autoImplicit false
open DecrAlmostLinearSSSP.Decremental

theorem solution : ∃ (p : Program) (C : ℝ) (a : ℕ → ℝ),
    0 < C ∧ Subpolynomial a ∧ ∀ i : Input, i.Valid →
      i.accuracy ≤ 1/(i.size : ℝ) → Maintains p C a 9 true i := by
  refine ⟨Exact.Dijkstra.hostProgram,10000,Exact.Dijkstra.overhead,by norm_num,?_,?_⟩
  · exact DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_8.2.2.2.2.1.1
  · exact DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_8.2.2.2.2.2.2.2
