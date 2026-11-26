-- Prove2me | solution 1 for FD1D.leafCount_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:00:20.347798+00:00
-- url     : https://prove2.me/submissions/2f1ca84a-a8a7-4bc5-a050-9379fef28137

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Parameters

set_option autoImplicit true
open FD1D
noncomputable section
open Filter Asymptotics
namespace FD1D
theorem _root_.solution (m : ℕ) :
    leafCount m = 2 ^ treeDepth m :=
  rfl
end FD1D
