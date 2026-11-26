-- Prove2me | solution 1 for FD1D.policyA_eq_parameterA
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:59:48.850945+00:00
-- url     : https://prove2.me/submissions/b09df298-89eb-4f4f-9884-54a601f0d6db

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Parameters

set_option autoImplicit true
open FD1D
noncomputable section
open Filter Asymptotics
namespace FD1D
theorem _root_.solution (m : ℕ) :
    policyA m = parameterA m := by
  unfold policyA parameterA
  rw [← Real.natCeil_logb_natCast 2 (m + 1)]
  norm_num
end FD1D
