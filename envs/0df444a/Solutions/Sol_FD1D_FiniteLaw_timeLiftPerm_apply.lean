-- Prove2me | solution 1 for FD1D.FiniteLaw.timeLiftPerm_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:43:59.799705+00:00
-- url     : https://prove2.me/submissions/330a3802-409a-4ec2-8913-2510ea5a4215

import Definitions.Def_FD1D_Expectations
import Definitions.Def_FD1D_Averaging

set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators
open FD1D.FiniteLaw
variable {α : Type*} [Fintype α]
namespace FD1D.FiniteLaw
theorem _root_.solution {T : ℕ} (e : Equiv.Perm α)
    (t : Fin T) (x : α) :
    timeLiftPerm e (t, x) = (t, e x) :=
  rfl
end FD1D.FiniteLaw
