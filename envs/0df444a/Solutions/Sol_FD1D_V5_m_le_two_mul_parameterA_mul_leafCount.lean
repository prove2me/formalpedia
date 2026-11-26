-- Prove2me | solution 1 for FD1D.V5.m_le_two_mul_parameterA_mul_leafCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:49:25.386308+00:00
-- url     : https://prove2.me/submissions/e6ab247d-cb2f-4ba1-a690-5803e7e34084

import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_V5_Parameters
import Theorems.Thm_FD1D_V5_parameterA_pos
import Theorems.Thm_FD1D_V5_parameterQuotient_lt_two_mul_leafCount

set_option autoImplicit true
open FD1D FD1D.V5
noncomputable section
open Filter Asymptotics
namespace FD1D.V5
theorem _root_.solution {m : ℕ} (hm : 1 ≤ m) :
    m ≤ 2 * parameterA m * leafCount m := by
  have hlt : m < (2 * leafCount m) * parameterA m :=
    (Nat.div_lt_iff_lt_mul (parameterA_pos hm)).mp
      (parameterQuotient_lt_two_mul_leafCount m)
  calc
    m ≤ (2 * leafCount m) * parameterA m := Nat.le_of_lt hlt
    _ = 2 * parameterA m * leafCount m := by ac_rfl
end FD1D.V5
