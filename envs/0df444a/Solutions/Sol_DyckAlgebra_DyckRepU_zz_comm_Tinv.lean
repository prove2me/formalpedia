-- Prove2me | solution 1 for DyckAlgebra.DyckRepU.zz_comm_Tinv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:19:04.877181+00:00
-- url     : https://prove2.me/submissions/bbdb3d0c-ecd5-4a3f-b181-88f613e30971

import Definitions.Def_RequestProject_Aqt_Rep
import Definitions.Def_RequestProject_Aqt_Theta

set_option autoImplicit true
open DyckAlgebra
open scoped BigOperators
universe v
attribute [instance] ThetaData.ring ThetaData.algebra
open DyckAlgebra.DyckRepU
variable {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2)
namespace DyckAlgebra.DyckRepU
theorem _root_.solution (i j : ℕ) (h : i ≠ j ∧ i ≠ j + 1) :
    ρ.zz i * ρ.Tinv j = ρ.Tinv j * ρ.zz i := by
  have h_comm : ρ.zz i * ρ.T j = ρ.T j * ρ.zz i := by
    exact ρ.zTcomm i j h;
  have h_comm_inv : ρ.Tinv j * ρ.T j = 1 := by
    exact ρ.TinvR j;
  have h_comm_inv : ρ.T j * ρ.Tinv j = 1 := by
    exact ρ.TinvL j;
  apply_fun ( · * ρ.Tinv j ) at h_comm;
  grind
end DyckAlgebra.DyckRepU
