-- Prove2me | solution 1 for Deformation.HondaSystem.finrank_selfExt_le_finrank_endHonda_add_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/4406f00b-14a0-54d8-a961-417176adbe45

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_HondaSelfExt
import Theorems.Thm_Deformation_HondaSystem_finrank_selfExt_eq_finrank_endHonda_of_L_eq_bot
import Theorems.Thm_Deformation_HondaSystem_finrank_selfExt_eq_finrank_endHonda_of_L_eq_top
import Theorems.Thm_Deformation_HondaSystem_finrank_selfExt_eq_one_add_finrank_endHonda
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_HondaSystem_finrank_selfExt_le_finrank_endHonda_add_one

set_option autoImplicit false
set_option maxHeartbeats 800000

universe u v

open LinearMap Submodule Function

open Deformation Deformation.HondaSystem in

theorem solution
    {k : Type u} [Field k] {D : Type v} [AddCommGroup D] [Module k D]
    [FiniteDimensional k D] {ℓ : k} (hℓ : ℓ = 0) (H : Deformation.HondaSystem ℓ D)
    (hD : Module.finrank k D = 2) :
    Module.finrank k H.selfExt ≤ Module.finrank k H.endHonda + 1 := by
  have hLle : Module.finrank k H.L ≤ 2 := hD ▸ Submodule.finrank_le H.L
  rcases Nat.lt_or_ge (Module.finrank k H.L) 1 with h0 | h1
  ·
    have hL : H.L = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
    rw [Deformation.HondaSystem.finrank_selfExt_eq_finrank_endHonda_of_L_eq_bot hℓ H hL]
    exact Nat.le_succ _
  rcases Nat.lt_or_ge (Module.finrank k H.L) 2 with h1' | h2
  ·
    have hL1 : Module.finrank k H.L = 1 := by omega
    rw [Deformation.HondaSystem.finrank_selfExt_eq_one_add_finrank_endHonda hℓ H hD hL1]
    omega
  ·
    have hL : H.L = ⊤ := Submodule.eq_top_of_finrank_eq (by omega)
    rw [Deformation.HondaSystem.finrank_selfExt_eq_finrank_endHonda_of_L_eq_top hℓ H hL]
    exact Nat.le_succ _

end S_Deformation_HondaSystem_finrank_selfExt_le_finrank_endHonda_add_one
end P2MW
export P2MW.S_Deformation_HondaSystem_finrank_selfExt_le_finrank_endHonda_add_one (solution)
