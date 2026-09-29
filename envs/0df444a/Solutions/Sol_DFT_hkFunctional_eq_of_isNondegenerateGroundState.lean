-- Prove2me | solution 1 for DFT.hkFunctional_eq_of_isNondegenerateGroundState
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:34:24.258245+00:00
-- url     : https://prove2.me/submissions/2da40adf-6bda-40a0-9df5-c95e821024ec

import Definitions.Def_DFT_HohenbergKohn

open MeasureTheory
open DFT

namespace Ag3Aux_HKFunc

theorem uniq (M : HKModel) {v₁ v₂ : M.Pot} {Ψ₁ Ψ₂ : M.Wf}
    (h₁ : M.IsNondegenerateGroundState v₁ Ψ₁) (h₂ : M.IsNondegenerateGroundState v₂ Ψ₂)
    (hd : M.dens Ψ₁ = M.dens Ψ₂) : Ψ₁ = Ψ₂ := by
  by_contra hne
  have a := h₁ Ψ₂ (Ne.symm hne)
  have b := h₂ Ψ₁ hne
  unfold HKModel.energy at a b
  rw [hd] at a b
  linarith

end Ag3Aux_HKFunc

open Ag3Aux_HKFunc

theorem solution (M : HKModel) {v : M.Pot} {Ψ : M.Wf}
    (h : M.IsNondegenerateGroundState v Ψ) : M.hkFunctional (M.dens Ψ) = M.F Ψ := by
  have hv : M.VRepresentable (M.dens Ψ) := ⟨Ψ, ⟨v, h⟩, rfl⟩
  unfold HKModel.hkFunctional
  rw [dif_pos hv]
  obtain ⟨⟨v', h'⟩, hd⟩ := hv.choose_spec
  rw [uniq M h' h hd]
