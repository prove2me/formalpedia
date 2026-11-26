-- Prove2me | solution 1 for FD1D.V5.LocalPolicy.bellman_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:48:35.553971+00:00
-- url     : https://prove2.me/submissions/7c800f24-2b19-4057-82f2-f57e39485e19

import Definitions.Def_FD1D_V5_Parameters
import Definitions.Def_FD1D_V5_LocalPolicy

set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalPolicy
noncomputable section
namespace FD1D.V5.LocalPolicy
theorem _root_.solution {h t Z : ℝ}
    (hZ : 0 ≤ Z) (ht : t ≤ h / 2) :
    bellman h t Z ≤ 0 := by
  unfold bellman
  have hfirst : (t - h / 2) * Z ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) hZ
  nlinarith [sq_nonneg t]
end FD1D.V5.LocalPolicy
