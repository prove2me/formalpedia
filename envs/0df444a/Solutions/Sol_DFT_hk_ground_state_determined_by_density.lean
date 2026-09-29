-- Prove2me | solution 1 for DFT.hk_ground_state_determined_by_density
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:33:35.355333+00:00
-- url     : https://prove2.me/submissions/51e0b628-2a38-46d8-a611-9873526671bb

import Definitions.Def_DFT_HohenbergKohn

open MeasureTheory
open DFT

theorem solution (M : HKModel) {v₁ v₂ : M.Pot} {Ψ₁ Ψ₂ : M.Wf}
    (h₁ : M.IsNondegenerateGroundState v₁ Ψ₁) (h₂ : M.IsNondegenerateGroundState v₂ Ψ₂)
    (hd : M.dens Ψ₁ = M.dens Ψ₂) : Ψ₁ = Ψ₂ := by
  by_contra hne
  have a := h₁ Ψ₂ (Ne.symm hne)
  have b := h₂ Ψ₁ hne
  unfold HKModel.energy at a b
  rw [hd] at a b
  linarith
