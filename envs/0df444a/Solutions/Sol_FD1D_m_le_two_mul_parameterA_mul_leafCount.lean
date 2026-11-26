-- Prove2me | solution 1 for FD1D.m_le_two_mul_parameterA_mul_leafCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:23:50.556324+00:00
-- url     : https://prove2.me/submissions/7944db2b-8d52-4375-a769-6ddf6fa0e000

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Parameters
import Theorems.Thm_FD1D_parameterA_pos
import Theorems.Thm_FD1D_parameterQuotient_lt_two_mul_leafCount

set_option autoImplicit true
open FD1D
noncomputable section
open Filter Asymptotics
namespace FD1D
theorem _root_.solution {m : ℕ} (hm : 1 ≤ m) :
    m ≤ 2 * parameterA m * leafCount m := by
  have hlt : m < (2 * leafCount m) * parameterA m :=
    (Nat.div_lt_iff_lt_mul (parameterA_pos hm)).mp
      (parameterQuotient_lt_two_mul_leafCount m)
  calc
    m ≤ (2 * leafCount m) * parameterA m := Nat.le_of_lt hlt
    _ = 2 * parameterA m * leafCount m := by ac_rfl
end FD1D
